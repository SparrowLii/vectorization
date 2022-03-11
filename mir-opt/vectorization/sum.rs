#![feature(rustc_attrs)]
pub fn main() {
    use std::time;
    const LEN: usize = 51200;
    let mut v: [f32; LEN] = [0.; LEN];
    for i in 0..LEN {
        v[i] = ((i * i - i) % 100) as f32;
    }

    let mut sum1 = 0.;
    let t1 = time::SystemTime::now();
    for _ in 0..100 {
        sum1 = func1(&v);
    }
    let t1 = time::SystemTime::now().duration_since(t1).unwrap().as_micros();

    let mut sum2 = 0.;
    let t2 = time::SystemTime::now();
    for _ in 0..100 {
        sum2 = func2(&v);
    }
    let t2 = time::SystemTime::now().duration_since(t2).unwrap().as_micros();

    println!("t1: {}", t1);
    println!("t2: {}", t2);
    println!("ans1: {}", sum1);
    println!("ans2: {}", sum2);

}

// EMIT_MIR sum.func1.Vectorize.before.mir
// EMIT_MIR sum.func1.Vectorize.after.mir
#[vectorization]
fn func1(arr: &[f32]) -> f32 {
    let mut sum = 0.;
    for i in arr {
        sum += *i;
    }
    sum
}

fn func2(arr: &[f32]) -> f32 {
    let mut sum = 0.;
    for i in arr {
        sum += *i;
    }
    sum
}
