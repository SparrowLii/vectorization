
pub fn main() {
    let mut src2: [u32; 224] = [0; 224];
    for i in 0..224 {
        src2[i] = i as u32;
    }
    let mut src: [u8; 224] = src2.map(|i| i as u8);
    let mut val: [u32; 224] = [0; 224];
    func1(&src, &src2, &mut val);
    println!("{}", val[0]);
}

// EMIT_MIR iter_simd.func1.Vectorize.before.mir
// EMIT_MIR iter_simd.func1.Vectorize.after.mir

fn func1(src: &[u8], src2: &[u32], val: &mut [u32]) {
    let mut sum = 0;
    for x in 0..src.len() {
        let v = src[x] as u32;
        sum += v * v;
        val[x] = src2[x] + sum;
    }
}
