// Copyright 2016 Brian Smith.
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

//! [chacha20-poly1305@openssh.com], authenticated encryption using two Chacha20
//! keys and one (derived) Poly1305 key.
//!
//! [chacha20-poly1305@openssh.com]:
//!    http://cvsweb.openbsd.org/cgi-bin/cvsweb/src/usr.bin/ssh/PROTOCOL.chacha20poly1305?annotate=HEAD

use {chacha, error, poly1305};

/// A key for sealing a chacha20-poly1305@openssh.com packet.
pub struct SealingKey {
    key: Key,
}

impl SealingKey {
    /// Constructs a new `SealingKey`.
    pub fn new(key_material: &[u8; KEY_LEN]) -> SealingKey {
        SealingKey { key: Key::new(key_material) }
    }

    /// Seals a packet.
    pub fn seal_in_place(&self, sequence_number: u32,
                         plaintext_in_ciphertext_out: &mut [u8],
                         tag_out: &mut [u8; TAG_LEN]) {
        let mut counter = make_counter(sequence_number);

        {
            let (len_in_out, data_and_padding_in_out) =
                plaintext_in_ciphertext_out.split_at_mut(PACKET_LENGTH_LEN);

            chacha::chacha20_xor_in_place(&self.key.k_1, &counter, len_in_out);

            counter[0] = 1;
            chacha::chacha20_xor_in_place(&self.key.k_2, &counter,
                                          data_and_padding_in_out);
        }

        let mut poly_key = [0; poly1305::KEY_LEN];
        counter[0] = 0;
        chacha::chacha20_xor_in_place(&self.key.k_2, &counter, &mut poly_key);
        poly1305::sign(&poly_key, plaintext_in_ciphertext_out, tag_out);
    }
}

/// A key for opening a chacha20-poly1305@openssh.com packet.
pub struct OpeningKey {
    key: Key,
}

impl OpeningKey {
    /// Constructs a new `OpeningKey`.
    pub fn new(key_material: &[u8; KEY_LEN]) -> OpeningKey {
        OpeningKey { key: Key::new(key_material) }
    }

    /// Decrypts a packet length.
    pub fn decrypt_packet_length(
            &self, sequence_number: u32,
            encrypted_packet_length: [u8; PACKET_LENGTH_LEN])
            -> [u8; PACKET_LENGTH_LEN] {
        let mut packet_length = encrypted_packet_length;
        let counter = make_counter(sequence_number);
        chacha::chacha20_xor_in_place(&self.key.k_1, &counter,
                                      &mut packet_length);
        packet_length
    }

    /// Opens (authenticates and decrypts) a packet.
    ///
    /// `ciphertext_in_plaintext_out` must be of the form
    /// `encrypted_packet_length||ciphertext`. If the function returns
    /// successfully, `ciphertext_in_plaintext_out[PACKET_LENGTH_LEN..] will
    /// contain the plaintext of the packet contents.
    pub fn open_in_place(&self, sequence_number: u32,
                         ciphertext_in_plaintext_out: &mut [u8],
                         tag: &[u8; TAG_LEN])
                         -> Result<(), error::Unspecified> {
        let mut counter = make_counter(sequence_number);

        let mut poly_key = [0; poly1305::KEY_LEN];
        chacha::chacha20_xor_in_place(&self.key.k_2, &counter, &mut poly_key);

        try!(poly1305::verify(&poly_key, ciphertext_in_plaintext_out, tag));

        // The first `PACKET_LENGTH_LEN` bytes were encrypted with self.key.k_1
        // and were already decrypted with decrypt_packet_length.
        counter[0] = 1;
        chacha::chacha20_xor_in_place(
            &self.key.k_2, &counter,
            &mut ciphertext_in_plaintext_out[PACKET_LENGTH_LEN..]);

        Ok(())
    }
}

struct Key {
    k_1: chacha::Key,
    k_2: chacha::Key,
}

impl Key {
    pub fn new(key_material: &[u8; KEY_LEN]) -> Key {
        Key {
            k_1: chacha::key_from_bytes(
                    slice_as_array_ref!(
                        &key_material[..chacha::KEY_LEN_IN_BYTES],
                        chacha::KEY_LEN_IN_BYTES).unwrap()),
            k_2: chacha::key_from_bytes(
                    slice_as_array_ref!(
                        &key_material[chacha::KEY_LEN_IN_BYTES..],
                        chacha::KEY_LEN_IN_BYTES).unwrap()),
        }
    }
}

fn make_counter(sequence_number: u32) -> chacha::Counter {
    let mut sequence_number = sequence_number;
    let mut nonce = [0; chacha::NONCE_LEN];
    for i in 0..4 {
        nonce[chacha::NONCE_LEN - (4 - i)] = (sequence_number % 0x100) as u8;
        sequence_number /= 0x100;
    }
    chacha::make_counter(&nonce, 0)
}

/// The length of chacha20-poly1305@openssh.com key.
pub const KEY_LEN: usize = chacha::KEY_LEN_IN_BYTES * 2;

/// The length of a  chacha20-poly1305@openssh.com tag.
pub const TAG_LEN: usize = poly1305::TAG_LEN;

/// The length in bytes of the `packet_length` field in a SSH packet.
pub const PACKET_LENGTH_LEN: usize = 4; // 32 bits
