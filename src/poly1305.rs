// Copyright 2015-2016 Brian Smith.
//
// Permission to use, copy, modify, and/or distribute this software for any
// purpose with or without fee is hereby granted, provided that the above
// copyright notice and this permission notice appear in all copies.
//
// THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHORS DISCLAIM ALL WARRANTIES
// WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY
// SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
// WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
// OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
// CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

//! TODO: Docs

//! TODO: enforce maximum input length.

use {c, constant_time, error};

/// TODO: Docs
pub struct SigningContext {
    state: [u8; STATE_LEN],
}

impl SigningContext {
    /// TODO: Docs
    #[inline]
    pub fn with_key(key: &[u8; KEY_LEN]) -> SigningContext {
        let mut ctx = SigningContext {
            state: [0u8; STATE_LEN],
        };
        unsafe { GFp_poly1305_init(&mut ctx.state, key); }
        ctx
    }

    /// TODO: Docs
    #[inline]
    pub fn update(&mut self, input: &[u8]) {
        unsafe {
            GFp_poly1305_update(&mut self.state, input.as_ptr(), input.len());
        }
    }

    /// TODO: Docs
    #[inline]
    pub fn sign(mut self, tag_out: &mut [u8; TAG_LEN]) {
        unsafe { GFp_poly1305_finish(&mut self.state, tag_out); }
    }
}

/// TODO: docs
pub fn verify(key: &[u8; KEY_LEN], msg: &[u8], tag: &[u8])
              -> Result<(), error::Unspecified> {
    let mut calculated_tag = [0u8; TAG_LEN];
    sign(key, msg, &mut calculated_tag);
    constant_time::verify_slices_are_equal(&calculated_tag[..], tag)
}

/// TODO: docs
pub fn sign(key: &[u8; KEY_LEN], msg: &[u8], tag: &mut [u8; TAG_LEN]) {
    let mut ctx = SigningContext::with_key(key);
    ctx.update(msg);
    ctx.sign(tag)
}

/// The length of a Poly1305 key.
pub const KEY_LEN: usize = 32;

/// The length of a Poly1305 Tag.
pub const TAG_LEN: usize = 128 / 8;

const STATE_LEN: usize = 256;

extern {
    fn GFp_poly1305_init(state: &mut [u8; STATE_LEN], key: &[u8; KEY_LEN]);
    fn GFp_poly1305_finish(state: &mut [u8; STATE_LEN],
                           mac: &mut [u8; TAG_LEN]);
    fn GFp_poly1305_update(state: &mut [u8; STATE_LEN],
                           in_: *const u8, in_len: c::size_t);
}

#[cfg(test)]
mod tests {
    use c;

    bssl_test!(test_poly1305, bssl_poly1305_test_main);

    #[test]
    pub fn test_poly1305_state_len() {
        assert_eq!((super::STATE_LEN + 255) / 256,
                   (unsafe { GFp_POLY1305_STATE_LEN } + 255) / 256);
    }

    extern {
        static GFp_POLY1305_STATE_LEN: c::size_t;
    }
}
