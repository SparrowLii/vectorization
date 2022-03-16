#![feature(rustc_attrs)]
pub fn main() {
    const LEN: usize = 224 * 224;
    use std::time;
    let mut src2: [f32; LEN] = [0.; LEN];
    for i in 0..LEN {
        src2[i] = (i * (LEN - i + 1)) as f32;
    }
    let src: [f32; LEN] = src2.map(|i| i);
    let mut val: [f32; LEN] = [0.; LEN];
    let mut val2: [f32; LEN] = [0.; LEN];

    let t1 = time::SystemTime::now();
    for _ in 0..100 {
        func1(&src, &val.clone(), &mut val);
    }
    let t1 = time::SystemTime::now().duration_since(t1).unwrap().as_micros();

    let t2 = time::SystemTime::now();
    for _ in 0..100 {
        func2(&src, &val2.clone(), &mut val2);
    }
    let t2 = time::SystemTime::now().duration_since(t2).unwrap().as_micros();

    assert_eq!(val, val2);

    println!("t1: {}", t1);
    //println!("val1: {:?}", &val[0..20]);
    println!("t2: {}", t2);
}

// EMIT_MIR iter_simd.func1.Vectorize.before.mir
// EMIT_MIR iter_simd.func1.Vectorize.after.mir
#[vectorization]
fn func1(src: &[f32], src2: &[f32], val: &mut [f32]) {
    let mut sum = 0.;
    for x in 0..src.len() {
        let v = src[x];
        sum += v * v;
        val[x] = src2[x] + sum;
    }
}

fn func2(src: &[f32], src2: &[f32], val: &mut [f32]) {
    let mut sum = 0.;
    for x in 0..src.len() {
        let v = src[x];
        sum += v * v;
        val[x] = src2[x] + sum;
    }
}
