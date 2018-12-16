#![no_std]
pub extern crate block_cipher_trait;
extern crate byte_tools;
#[macro_use]
extern crate opaque_debug;

use core::fmt;
use core::marker::PhantomData;

use block_cipher_trait::generic_array::typenum::{U1, U56, U8};
use block_cipher_trait::generic_array::GenericArray;
pub use block_cipher_trait::BlockCipher;
use block_cipher_trait::InvalidKeyLength;

mod consts;

type Block = GenericArray<u8, U8>;
type BlowfishBE = Blowfish<BE>;
type BlowfishLE = Blowfish<LE>;

mod private {
    trait Sealed {}
    impl Sealed for super::BE {}
    impl Sealed for super::LE {}
}

pub trait Endianess {
    fn write_u32(dst: &mut [u8], n: u32);
    fn read_u32(src: &[u8]) -> u32;
}
pub struct BE;
impl Endianess for BE {
    #[inline]
    fn write_u32(dst: &mut [u8], n: u32) { byte_tools::write_u32_be(dst, n); }
    #[inline]
    fn read_u32(src: &[u8]) -> u32 { byte_tools::read_u32_be(src) }
}
pub struct LE;
impl Endianess for LE {
    #[inline]
    fn write_u32(dst: &mut [u8], n: u32) { byte_tools::write_u32_le(dst, n); }
    #[inline]
    fn read_u32(src: &[u8]) -> u32 { byte_tools::read_u32_le(src) }
}

#[derive(Clone, Copy)]
pub struct Blowfish<T: Endianess = BE> {
    s: [[u32; 256]; 4],
    p: [u32; 18],
    _pd: PhantomData<T>,
}

fn next_u32_wrap(buf: &[u8], offset: &mut usize) -> u32 {
    let mut v = 0;
    for _ in 0..4 {
        if *offset >= buf.len() {
            *offset = 0;
        }
        v = (v << 8) | buf[*offset] as u32;
        *offset += 1;
    }
    v
}

impl<T: Endianess> Blowfish<T> {
    fn init_state() -> Blowfish<T> {
        Blowfish {
            p: consts::P,
            s: consts::S,
            _pd: PhantomData,
        }
    }

    fn expand_key(&mut self, key: &[u8]) {
        let mut key_pos = 0;
        for i in 0..18 {
            self.p[i] ^= next_u32_wrap(key, &mut key_pos);
        }
        let mut lr = (0u32, 0u32);
        for i in 0..9 {
            lr = self.encrypt(lr.0, lr.1);
            self.p[2 * i] = lr.0;
            self.p[2 * i + 1] = lr.1;
        }
        for i in 0..4 {
            for j in 0..128 {
                lr = self.encrypt(lr.0, lr.1);
                self.s[i][2 * j] = lr.0;
                self.s[i][2 * j + 1] = lr.1;
            }
        }
    }

    fn round_function(&self, x: u32) -> u32 {
        let a = self.s[0][(x >> 24) as usize];
        let b = self.s[1][((x >> 16) & 0xff) as usize];
        let c = self.s[2][((x >> 8) & 0xff) as usize];
        let d = self.s[3][(x & 0xff) as usize];
        (a.wrapping_add(b) ^ c).wrapping_add(d)
    }

    fn encrypt(&self, mut l: u32, mut r: u32) -> (u32, u32) {
        for i in 0..8 {
            l ^= self.p[2 * i];
            r ^= self.round_function(l);
            r ^= self.p[2 * i + 1];
            l ^= self.round_function(r);
        }
        l ^= self.p[16];
        r ^= self.p[17];
        (r, l)
    }

    fn decrypt(&self, mut l: u32, mut r: u32) -> (u32, u32) {
        for i in (1..9).rev() {
            l ^= self.p[2 * i + 1];
            r ^= self.round_function(l);
            r ^= self.p[2 * i];
            l ^= self.round_function(r);
        }
        l ^= self.p[1];
        r ^= self.p[0];
        (r, l)
    }
}

impl<T: Endianess> BlockCipher for Blowfish<T> {
    type KeySize = U56;
    type BlockSize = U8;
    type ParBlocks = U1;

    fn new(key: &GenericArray<u8, U56>) -> Self {
        Self::new_varkey(&key).unwrap()
    }

    fn new_varkey(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if key.len() < 4 || key.len() > 56 {
            return Err(InvalidKeyLength);
        }
        let mut blowfish = Blowfish::init_state();
        blowfish.expand_key(key);
        Ok(blowfish)
    }

    #[inline]
    fn encrypt_block(&self, block: &mut Block) {
        let l = T::read_u32(&block[..4]);
        let r = T::read_u32(&block[4..]);
        let (l, r) = self.encrypt(l, r);
        T::write_u32(&mut block[..4], l);
        T::write_u32(&mut block[4..], r);
    }

    #[inline]
    fn decrypt_block(&self, block: &mut Block) {
        let l = T::read_u32(&block[..4]);
        let r = T::read_u32(&block[4..]);
        let (l, r) = self.decrypt(l, r);
        T::write_u32(&mut block[..4], l);
        T::write_u32(&mut block[4..], r);
    }
}

/// Bcrypt extension of blowfish
#[cfg(feature = "bcrypt")]
impl<T: Endianess> Blowfish<T> {
    pub fn salted_expand_key(&mut self, salt: &[u8], key: &[u8]) {
        let mut key_pos = 0;
        for i in 0..18 {
            self.p[i] ^= next_u32_wrap(key, &mut key_pos);
        }
        let mut lr = (0u32, 0u32);
        let mut salt_pos = 0;
        for i in 0..9 {
            let lk = next_u32_wrap(salt, &mut salt_pos);
            let rk = next_u32_wrap(salt, &mut salt_pos);
            lr = self.encrypt(lr.0 ^ lk, lr.1 ^ rk);

            self.p[2 * i] = lr.0;
            self.p[2 * i + 1] = lr.1;
        }
        for i in 0..4 {
            for j in 0..64 {
                let lk = next_u32_wrap(salt, &mut salt_pos);
                let rk = next_u32_wrap(salt, &mut salt_pos);
                lr = self.encrypt(lr.0 ^ lk, lr.1 ^ rk);

                self.s[i][4 * j] = lr.0;
                self.s[i][4 * j + 1] = lr.1;

                let lk = next_u32_wrap(salt, &mut salt_pos);
                let rk = next_u32_wrap(salt, &mut salt_pos);
                lr = self.encrypt(lr.0 ^ lk, lr.1 ^ rk);

                self.s[i][4 * j + 2] = lr.0;
                self.s[i][4 * j + 3] = lr.1;
            }
        }
    }

    pub fn bc_init_state() -> Blowfish<T> { Blowfish::init_state() }

    pub fn bc_encrypt(&self, l: u32, r: u32) -> (u32, u32) {
        self.encrypt(l, r)
    }

    pub fn bc_expand_key(&mut self, key: &[u8]) { self.expand_key(key) }
}

impl_opaque_debug!(Blowfish);
