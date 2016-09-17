// Copyright 2016 David Judd.
// Copyright 2016 Brian Smith.
//
// Permission to use, copy, modify, and/or distribute this software for any
// purpose with or without fee is hereby granted, provided that the above
// copyright notice and this permission notice appear in all copies.
//
// THE SOFTWARE IS PROVIDED "AS IS" AND AND THE AUTHORS DISCLAIM ALL WARRANTIES
// WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY
// SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
// WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
// OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
// CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

//! RSA blinding parameter generation.

use {c, core, rand, error, rsa};
use limb::*;

const RSA_KEY_MAX_LIMBS: usize = rsa::RSA_PUBLIC_KEY_MODULUS_BITS_MAX / LIMB_BITS;

/// Params which specify the implementation strategy for random sampling from
/// an interval (0, max].
struct SamplingParams {
    // We generate random data to fill a slice of limbs, so if we want a number
    // of bits which isn't a multiple of LIMB_BITS, we need to mask off some
    // of the bits in the most significant limb.
    most_sig_limb_mask: Limb,

    // Assume `x` is of the form `0b100...`. This means:
    //
    //    x < 2**n - 2**(n-2) - 2**(n-3).
    //
    // This means that `3*x < 2**(n+1)`. Proof:
    //
    //  3*x < 3*(2**n - 2**(n-2) - 2**(n-3))
    //      < (2 + 1)*(2**n - 2**(n-2) - 2**(n-3))
    //      < 2*(2**n - 2**(n-2) - 2**(n-3)) + 2**n - 2**(n-2) - 2**(n-3)
    //      < 2**(n+1) - 2**(n-1) - 2**(n-2) + 2**n - 2**(n-2) - 2**(n-3)
    //      < 2**(n+1) + 2**n - 2**(n-1) - 2**(n-2) - 2**(n-2) - 2**(n-3)
    //      < 2**(n+1) + 2**n - 2**(n-1) - 2*(2**(n-2)) - 2**(n-3)
    //      < 2**(n+1) + 2**n - 2**(n-1) - 2**(n-1) - 2**(n-3)
    //      < 2**(n+1) + 2**n - 2*(2**(n-1)) - 2**(n-3)
    //      < 2**(n+1) + 2**n - 2**n - 2**(n-3)
    //      < 2**(n+1) - 2**(n-3)
    //
    // Then clearly 2**(n+1) - 2**(n-3) < 2**(n+1) since n is positive.
    //
    // This means that when `max` is of the form `0b100...`, we can generate a
    // value in the range [0, 2**(n+1)), which would fall into one of four
    // sub-intervals:
    //
    //    [0, max)          => Return the value as-is.
    //    [max, 2*max)      => Return `value - max`.
    //    [2*max, 3*max)    => Return `value - max - max`.
    //    [3*max, 2**(n+1)) => Generate a new random value and try again.
    //
    // This avoids biasing the result towards small values, which is what
    // reducing the random value (mod max) would do, while reducing the
    // probability that a new random value will be needed.
    //
    // Microbenchmarking suggests this can provide a ~33% speedup.
    reduce_when_over_bound: bool,

    // In order to carry about the `max == 0b100...` optimization described
    // above, we need to generate one random bit more than we want to keep.
    //
    // When the number of bits we want to keep is a multiple of LIMB_BITS,
    // that means we need to allocate space for an extra limb to store the
    // extra bit.
    extend_limbs_by_one: bool,
}

/// References a positive integer range `[1..max_exclusive)`.
/// `max_exclusive` is assumed to be public, not secret.
//
// TODO(DJ) Part of this code can potentially be pulled back into `super::limb`
// and shared with EC key generation, without unnecessarily complicating that,
// once specialization is stabilized.
struct Range<'a> {
    max_exclusive: &'a [Limb],
    sampling_params: &'a SamplingParams,
}

impl <'a> Range<'a> {

    /// Are these little-endian limbs within the range?
    ///
    /// Checks in constant time.
    pub fn are_limbs_within(&self, limbs: &[Limb]) -> bool {
        assert_eq!(self.max_exclusive.len(), limbs.len());

        let is_zero = limbs_are_zero_constant_time(limbs);
        let is_lt_max =
            limbs_less_than_limbs_constant_time(limbs, self.max_exclusive);

        is_zero == LimbMask::False && is_lt_max == LimbMask::True
    }

    /// Chooses a positive integer within the range and stores it into `dest`.
    ///
    /// This function is intended to be suitable for generating private keys.
    fn sample_into_limbs(&self, dest: &mut [Limb], rng: &rand::SecureRandom)
                         -> Result<(), error::Unspecified> {
        // Loosely based on [NSA Suite B Implementer's Guide to ECDSA]
        // Appendix A.1.2, and
        // [NSA Suite B Implementer's Guide to NIST SP 800-56A] Appendix B.2,
        // "Key Pair Generation by Testing Candidates".
        //
        // [NSA Suite B Implementer's Guide to ECDSA]: doc/ecdsa.pdf.
        // [NSA Suite B Implementer's Guide to NIST SP 800-56A]: doc/ecdh.pdf.

        assert_eq!(self.max_exclusive.len(), dest.len());

        // XXX: The value 100 was chosen to match OpenSSL due to uncertainty of
        // what specific value would be better, but it seems bad to try 100
        // times.
        for _ in 0..100 {
            {
                let mut dest_as_bytes = limbs_as_bytes_mut(dest);
                try!(rng.fill(&mut dest_as_bytes));
            }

            {
                // Mask off unwanted bits
                let mask = self.sampling_params.most_sig_limb_mask;
                dest[self.max_exclusive.len() - 1] &= mask;
            }

            if self.are_limbs_within(&dest) {
                return Ok(());
            }

            if self.sampling_params.reduce_when_over_bound {
                // `dest` is not in (0, max] but maybe we can fix that.
                // (See above for explanation of why this is safe.)

                limbs_reduce_once_constant_time(dest, self.max_exclusive);
                if self.are_limbs_within(&dest) {
                    // `dest` was in [max, 2*max)
                    return Ok(());
                }

                limbs_reduce_once_constant_time(dest, self.max_exclusive);
                if self.are_limbs_within(&dest) {
                    // `dest` was in [2*max, 3*max)
                    return Ok(());
                }

                // `dest` was in [3*max, 2**(n+1)) or zero
            }
        }

        Err(error::Unspecified)
    }
}

#[allow(unsafe_code)]
#[allow(non_snake_case)]
#[doc(hidden)]
#[no_mangle]
pub unsafe extern fn GFp_rand_mod(dest: *mut Limb, max_exclusive: *const Limb,
                                  num_limbs: c::size_t, rng: *mut rand::RAND)
                                  -> c::int {
    const ERR: c::int = 0;
    const SUCCESS: c::int = 1;

    let max_exclusive = core::slice::from_raw_parts(max_exclusive, num_limbs);
    let mut dest = core::slice::from_raw_parts_mut(dest, num_limbs);

    let result = set_to_rand_mod(&mut dest, &max_exclusive, (*rng).rng);
    if result.is_err() {
        return ERR;
    }

    SUCCESS
}

/// Chooses a positive integer less than `max_exclusive` uniformly at random
/// and stores it into `dest`.
fn set_to_rand_mod(dest: &mut [Limb], max_exclusive: &[Limb], rng: &rand::SecureRandom)
            -> Result<(), error::Unspecified> {

    debug_assert_eq!(dest.len(), max_exclusive.len());

    let sampling_params = select_sampling_params(max_exclusive);

    if sampling_params.extend_limbs_by_one {
        with_extended_buffers(dest, max_exclusive, |ext_dest, ext_max| {
            let range = Range {
                max_exclusive: ext_max,
                sampling_params: &sampling_params,
            };
            range.sample_into_limbs(ext_dest, rng)
        })
    } else {
        let range = Range {
            max_exclusive: max_exclusive,
            sampling_params: &sampling_params,
        };
        range.sample_into_limbs(dest, rng)
    }
}

/// Copy `dest` and `max_exclusive` into temporary buffers which extend capacity
/// by one, pass those to the callback, then copy the modified destination
/// buffer back to `dest`.
fn with_extended_buffers<F>(dest: &mut [Limb], max_exclusive: &[Limb], cb: F)
                            -> Result<(), error::Unspecified>
                            where F: Fn(&mut [Limb], &[Limb])
                                     -> Result<(), error::Unspecified> {
    const BUF_SIZE: usize = RSA_KEY_MAX_LIMBS + 1;

    let buf_needed = dest.len() + 1;
    debug_assert_eq!(buf_needed, max_exclusive.len() + 1); // equivalent definition

    assert!(buf_needed <= BUF_SIZE);

    let mut tmp_max: [Limb; BUF_SIZE] = [0; BUF_SIZE];
    let mut tmp_dest: [Limb; BUF_SIZE] = [0; BUF_SIZE];

    tmp_dest[..dest.len()].copy_from_slice(&dest);
    tmp_max[..max_exclusive.len()].clone_from_slice(&max_exclusive);

    let result = cb(&mut tmp_dest[..buf_needed], &tmp_max[..buf_needed]);

    if result.is_ok() {
        let dest_len = dest.len();
        dest.clone_from_slice(&tmp_dest[..dest_len]);
    }

    result
}

/// Decide implementation strategy for random sampling - see `SamplingParams`.
fn select_sampling_params(max_exclusive: &[Limb]) -> SamplingParams {
    let starts_with_0b100 = starts_with_0b100_variable_time(max_exclusive);
    let leading_zeros = max_exclusive[max_exclusive.len() - 1].leading_zeros();

    if starts_with_0b100 && leading_zeros == 0 {
        SamplingParams {
            most_sig_limb_mask: 1, // effectively a carry into a new, more-significant limb
            reduce_when_over_bound: true,
            extend_limbs_by_one: true,
        }
    } else if starts_with_0b100 {
        SamplingParams {
            most_sig_limb_mask: Limb::max_value() >> (leading_zeros - 1),
            reduce_when_over_bound: true,
            extend_limbs_by_one: false,
        }
    } else {
        SamplingParams {
            most_sig_limb_mask: Limb::max_value() >> leading_zeros,
            reduce_when_over_bound: false,
            extend_limbs_by_one: false,
        }
    }
}

/// Does integer represented by limbs start with `0b100...`?
fn starts_with_0b100_variable_time(limbs: &[Limb]) -> bool {
    debug_assert!(limbs.len() > 0);

    let most_sig_limb = limbs[limbs.len() - 1];
    let next_limb = if limbs.len() > 1 {
        Some(limbs[limbs.len() - 2])
    } else {
        None
    };

    debug_assert!(most_sig_limb > 0);

    match most_sig_limb {
        4 => true,
        3 => false,
        2 => match next_limb {
            None => false,
            Some(l) => { l < (1 << (LIMB_BITS - 1)) },
        },
        1 => match next_limb {
            None => false,
            Some(l) => { l < (1 << (LIMB_BITS - 2)) },
        },
        _ => {
            // TODO(DJ) Eliminate `as`
            let used_bits = LIMB_BITS - (most_sig_limb.leading_zeros() as usize);
            let most_sig_bit = 1 << (used_bits - 1);
            most_sig_limb - most_sig_bit < most_sig_bit >> 2
        },
    }
}

#[cfg(test)]
mod tests {
    use {core,rand};
    use limb::*;

    #[test]
    fn test_select_sampling_params() {
        use super::select_sampling_params;

        for i in 0..LIMB_BITS {
            let x = 1 << i;

            let covering_mask = if i == LIMB_BITS - 1 {
                Limb::max_value()
            } else {
                (1 << (i + 1)) - 1
            };

            macro_rules! assert_uses_covering_mask {
                ( $b:expr ) => {
                    {
                        let p = select_sampling_params($b);
                        assert!(!p.reduce_when_over_bound, "for {:b}", x);
                        assert_eq!(covering_mask, p.most_sig_limb_mask);
                        assert!(!p.extend_limbs_by_one, "for: {:b}", x);
                    }
                }
            };

            macro_rules! assert_uses_extra_bit_mask_when_x_gte {
                ( $gte:expr, $b:expr ) => {
                    {
                        let extra_bit_available = covering_mask.count_zeros() > 0;
                        let extra_bit_mask = if extra_bit_available {
                            (covering_mask << 1) | 1
                        } else {
                            1
                        };

                        let p = select_sampling_params($b);
                        if x >= $gte {
                            assert!(p.reduce_when_over_bound, "for {:b}", x);
                            assert_eq!(extra_bit_mask, p.most_sig_limb_mask);
                            assert_eq!(!extra_bit_available, p.extend_limbs_by_one);
                        } else {
                            assert!(!p.reduce_when_over_bound, "for {:b}", x);
                            assert_eq!(covering_mask, p.most_sig_limb_mask);
                            assert!(!p.extend_limbs_by_one, "for: {:b}", x);
                        }
                    }
                }
            };

            let b = &[x];
            assert_uses_extra_bit_mask_when_x_gte!(0b100, b);

            let b = &[(x | 1)];
            assert_uses_extra_bit_mask_when_x_gte!(0b1000, b);

            let b = &[(x | x >> 1)];
            assert_uses_covering_mask!(b);

            let b = &[(x | x >> 2)];
            assert_uses_covering_mask!(b);

            let b = &[(x | x >> 3)];
            assert_uses_extra_bit_mask_when_x_gte!(0b100, b);

            let b = &[covering_mask];
            assert_uses_covering_mask!(b);
        }
    }

    #[test]
    fn test_limbs_in_range() {
        use super::{SamplingParams,Range};

        let params = SamplingParams {
            most_sig_limb_mask: Limb::max_value(),
            reduce_when_over_bound: false,
            extend_limbs_by_one: false,
        };

        let limbs = &[Limb::max_value(), Limb::max_value()];
        let range = Range { max_exclusive: limbs, sampling_params: &params };
        assert!(!range.are_limbs_within(&[Limb::max_value(),
                                          Limb::max_value()]));
        assert!(range.are_limbs_within(&[Limb::max_value(),
                                         Limb::max_value() - 1]));
        assert!(range.are_limbs_within(&[Limb::max_value() - 1,
                                         Limb::max_value()]));
        assert!(!range.are_limbs_within(&[0, 0]));
        assert!(range.are_limbs_within(&[1, 0]));
        assert!(range.are_limbs_within(&[0, 1]));

        let limbs = &[0x12345678, 0xdeadbeef];
        let range = Range { max_exclusive: limbs, sampling_params: &params };
        assert!(!range.are_limbs_within(&[0x12345678, 0xdeadbeef]));
        assert!(range.are_limbs_within(&[0x12345678 - 1, 0xdeadbeef]));
        assert!(range.are_limbs_within(&[0x12345678, 0xdeadbeef - 1]));
        assert!(!range.are_limbs_within(&[0x12345678 + 0x10, 0xdeadbeef]));
        assert!(!range.are_limbs_within(&[0x12345678, 0xdeadbeef + 0x10]));

        let limbs = &[0, 1];
        let range = Range { max_exclusive: limbs, sampling_params: &params };
        assert!(!range.are_limbs_within(&[0, 0]));
        assert!(range.are_limbs_within(&[1, 0]));
        assert!(!range.are_limbs_within(&[0, 1]));
        assert!(range.are_limbs_within(&[Limb::max_value(), 0]));

        let limbs = &[2];
        let range = Range { max_exclusive: limbs, sampling_params: &params };
        assert!(!range.are_limbs_within(&[0]));
        assert!(range.are_limbs_within(&[1]));
        assert!(!range.are_limbs_within(&[2]));
    }

    #[test]
    #[allow(unused_results)]
    fn test_set_to_rand_mod() {
        use super::set_to_rand_mod;

        let rng = rand::SystemRandom::new();

        macro_rules! generate_and_assert_success {
            ($limbs:expr, $num_limbs:expr) => { {
                let limbs: [Limb; $num_limbs] = $limbs;
                let mut dest: [Limb; $num_limbs] = [0; $num_limbs];
                assert!(set_to_rand_mod(&mut dest, &limbs, &rng).is_ok());
                assert!(dest.iter().any( |b| *b > 0 ));
                dest
            } }
        };

        generate_and_assert_success!([0xdeadbeef, 0xdeadbeef], 2);

        let dest = generate_and_assert_success!([2], 1);
        assert_eq!([1], dest);

        generate_and_assert_success!([1 << (LIMB_BITS - 1)], 1);
        generate_and_assert_success!([Limb::max_value()], 1);

        let dest = generate_and_assert_success!([0, 1], 2);
        assert_eq!(0, dest[1]);

        generate_and_assert_success!([1, 1], 2);
        generate_and_assert_success!([1 << (LIMB_BITS - 1), 1], 2);
        generate_and_assert_success!([Limb::max_value(), 1], 2);
        generate_and_assert_success!([0, 1 << (LIMB_BITS - 1)], 2);
        generate_and_assert_success!([1, 1 << (LIMB_BITS - 1)], 2);
        generate_and_assert_success!([1 << (LIMB_BITS - 1), 1 << (LIMB_BITS - 1)], 2);
        generate_and_assert_success!([Limb::max_value(), 1 << (LIMB_BITS - 1)], 2);
        generate_and_assert_success!([0, Limb::max_value()], 2);
        generate_and_assert_success!([1, Limb::max_value()], 2);
        generate_and_assert_success!([1 << (LIMB_BITS - 1), Limb::max_value()], 2);
        generate_and_assert_success!([Limb::max_value(), Limb::max_value()], 2);
    }

    #[test]
    fn test_random_generation_retries() {
        use super::{SamplingParams, Range};

        // Generates a string of bytes 0x00...00, which will always result in
        // a scalar value of zero.
        let random_00 = rand::test_util::FixedByteRandom { byte: 0 };

        // Generates a string of bytes 0xFF...FF, which will be larger than the
        // group order of any curve that is supported.
        let random_ff = rand::test_util::FixedByteRandom { byte: 0xff };

        let max_exclusive = [Limb::max_value(), Limb::max_value() >> 1];

        let sampling_params = SamplingParams {
            most_sig_limb_mask: Limb::max_value(),
            reduce_when_over_bound: false,
            extend_limbs_by_one: false,
        };

        let range = Range {
            max_exclusive: &max_exclusive,
            sampling_params: &sampling_params,
        };

        // Test that a generated zero is rejected and that `sample_into_limbs`
        // gives up after a while of only getting zeros.
        {
            let mut result = [0, 0];
            assert!(range.sample_into_limbs(&mut result, &random_00).is_err());
        }

        // Test that a generated value larger than `max_exclusive` is rejected
        // and that `sample_into_limbs` gives up after a while of only getting
        // values larger than the group order.
        {
            let mut result = [0, 0];
            assert!(range.sample_into_limbs(&mut result, &random_ff).is_err());
        }

        // Test that a generated value exactly equal `max_exclusive` is
        // rejected and that `generate` gives up after a while of only getting
        // that value from the PRNG.
        let max_exclusive_bytes = limbs_as_bytes(&max_exclusive);
        {
            let rng = rand::test_util::FixedSliceRandom {
                bytes: &max_exclusive_bytes
            };
            let mut result = [0, 0];
            assert!(range.sample_into_limbs(&mut result, &rng).is_err());
        }

        let max_exclusive_minus_1 = [max_exclusive[0] - 1, max_exclusive[1]];

        // Test that a generated value exactly equal to `mex_exclusive - 1` is
        // accepted.
        let max_exclusive_minus_1_bytes =
            limbs_as_bytes(&max_exclusive_minus_1);
        {
            let rng = rand::test_util::FixedSliceRandom {
                bytes: max_exclusive_minus_1_bytes
            };
            let mut result = [0, 0];
            range.sample_into_limbs(&mut result, &rng).unwrap();
            assert_eq!(&max_exclusive_minus_1, &result);
        }

        // Test recovery from initial RNG failure.
        {
            let bytes = [
                &max_exclusive_bytes[..],
                &[0u8; 2 * LIMB_BYTES],
                &max_exclusive_minus_1_bytes[..],
            ];
            let rng = rand::test_util::FixedSliceSequenceRandom {
                bytes: &bytes,
                current: core::cell::UnsafeCell::new(0),
            };
            let mut result = [0, 0];
            range.sample_into_limbs(&mut result, &rng).unwrap();
            assert_eq!(&max_exclusive_minus_1, &result);
        }
    }

    #[test]
    fn test_starts_with_0b100() {
        use super::starts_with_0b100_variable_time;

        assert!(!starts_with_0b100_variable_time(&[1]));
        assert!(!starts_with_0b100_variable_time(&[2]));
        assert!(!starts_with_0b100_variable_time(&[3]));
        assert!(starts_with_0b100_variable_time(&[4]));
        assert!(!starts_with_0b100_variable_time(&[5]));
        assert!(!starts_with_0b100_variable_time(&[6]));
        assert!(!starts_with_0b100_variable_time(&[7]));
        assert!(starts_with_0b100_variable_time(&[8]));
        assert!(starts_with_0b100_variable_time(&[9]));
        assert!(!starts_with_0b100_variable_time(&[10]));

        assert!(starts_with_0b100_variable_time(&[0, 1]));
        assert!(starts_with_0b100_variable_time(&[Limb::max_value() >> 2, 1]));
        assert!(!starts_with_0b100_variable_time(&[Limb::max_value() >> 1, 1]));
        assert!(starts_with_0b100_variable_time(&[Limb::max_value() >> 1, 2]));
        assert!(!starts_with_0b100_variable_time(&[Limb::max_value(), 2]));
        assert!(!starts_with_0b100_variable_time(&[Limb::max_value() >> 1, 3]));
        assert!(starts_with_0b100_variable_time(&[Limb::max_value(), 4]));
        assert!(!starts_with_0b100_variable_time(&[0, 5]));
        assert!(!starts_with_0b100_variable_time(&[0, 6]));
        assert!(!starts_with_0b100_variable_time(&[0, 7]));
        assert!(starts_with_0b100_variable_time(&[0, 8]));
        assert!(starts_with_0b100_variable_time(&[0, 9]));
        assert!(!starts_with_0b100_variable_time(&[0, 10]));
    }
}

#[cfg(feature = "internal_benches")]
mod bench {
    use {bench, rand};
    use limb::*;
    use super::{RSA_KEY_MAX_LIMBS, Range, SamplingParams, with_extended_buffers};

    #[bench]
    fn bench_sample_into_limbs_simple(b: &mut bench::Bencher) {
        let mut max: [Limb; RSA_KEY_MAX_LIMBS] = [0; RSA_KEY_MAX_LIMBS];
        max[RSA_KEY_MAX_LIMBS - 1] = 1 << (LIMB_BITS - 1);

        let mut dest: [Limb; RSA_KEY_MAX_LIMBS] = [0; RSA_KEY_MAX_LIMBS];
        let rng = rand::SystemRandom::new();

        let params = SamplingParams {
            most_sig_limb_mask: Limb::max_value(),
            reduce_when_over_bound: false,
            extend_limbs_by_one: false,
        };
        let range = Range {
            max_exclusive: &max,
            sampling_params: &params,
        };

        b.iter(|| {
            range.sample_into_limbs(&mut dest, &rng)
        });
    }

    #[bench]
    fn bench_sample_into_limbs_reduce_no_copy(b: &mut bench::Bencher) {
        let mut max: [Limb; RSA_KEY_MAX_LIMBS] = [0; RSA_KEY_MAX_LIMBS];
        max[RSA_KEY_MAX_LIMBS - 1] = 1 << (LIMB_BITS - 2);

        let mut dest: [Limb; RSA_KEY_MAX_LIMBS] = [0; RSA_KEY_MAX_LIMBS];
        let rng = rand::SystemRandom::new();

        let params = SamplingParams {
            most_sig_limb_mask: Limb::max_value(),
            reduce_when_over_bound: true,
            extend_limbs_by_one: false,
        };
        let range = Range {
            max_exclusive: &max,
            sampling_params: &params,
        };

        b.iter(|| {
            range.sample_into_limbs(&mut dest, &rng)
        });
    }

    #[bench]
    fn bench_sample_into_limbs_reduce_with_copy(b: &mut bench::Bencher) {
        let mut max: [Limb; RSA_KEY_MAX_LIMBS] = [0; RSA_KEY_MAX_LIMBS];
        max[RSA_KEY_MAX_LIMBS - 1] = 1 << (LIMB_BITS - 1);

        let mut dest: [Limb; RSA_KEY_MAX_LIMBS] = [0; RSA_KEY_MAX_LIMBS];
        let rng = rand::SystemRandom::new();

        let params = SamplingParams {
            most_sig_limb_mask: 1,
            reduce_when_over_bound: true,
            extend_limbs_by_one: true,
        };

        b.iter(|| {
            with_extended_buffers(&mut dest, &max, |ext_dest, ext_max| {
                let range = Range {
                    max_exclusive: ext_max,
                    sampling_params: &params,
                };
                range.sample_into_limbs(ext_dest, &rng)
            })
        });
    }
}
