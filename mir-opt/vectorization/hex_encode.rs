#![feature(rustc_attrs)]
const LEN: usize = 256000;
pub fn main() {
    let mut dst1 = [0; LEN];
    let mut dst2 = [0; LEN];

    let mut src = [0; LEN];
    for i in 0..LEN {
        src[i] = (i + 1) as u8;
    }
    use std::time;

    let t2 = time::SystemTime::now();
    for _ in 0..10 {
        hex_encode_2(&src, &mut dst2);
    }
    let t2 = time::SystemTime::now().duration_since(t2).unwrap().as_micros();

    let t1 = time::SystemTime::now();
    for _ in 0..10 {
        hex_encode(&src, &mut dst1);
    }
    let t1 = time::SystemTime::now().duration_since(t1).unwrap().as_micros();

    assert_eq!(dst1, dst2);

    println!("t1: {}", t1);
    println!("t2: {}", t2);

}

// EMIT_MIR hex_encode.hex_encode.Vectorize.before.mir
// EMIT_MIR hex_encode.hex_encode.Vectorize.after.mir
#[vectorization]
fn hex_encode(src: &[u8], dst: &mut [u8]) {
    fn hex(byte: u8) -> u8 {
        static TABLE: &[u8] = b"0123456789abcdef";
        TABLE[byte as usize]
    }

    for (byte, slots) in src.iter().zip(dst.chunks_mut(2)) {
        slots[0] = hex((*byte >> 4) & 0xf);
        slots[1] = hex(*byte & 0xf);
    }
}

fn hex_encode_2(src: &[u8], dst: &mut [u8]) {
    fn hex(byte: u8) -> u8 {
        static TABLE: &[u8] = b"0123456789abcdef";
        TABLE[byte as usize]
    }

    for (byte, slots) in src.iter().zip(dst.chunks_mut(2)) {
        slots[0] = hex((*byte >> 4) & 0xf);
        slots[1] = hex(*byte & 0xf);
    }
}
