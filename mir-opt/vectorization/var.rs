#![feature(rustc_attrs)]
pub fn main() {
    use std::time;
    const LEN: usize = 51200;
    let mut v: [f32; LEN] = [0.; LEN];
    for i in 0..LEN {
        v[i] = ((i * i - i) % 100) as f32;
    }

    let t1 = time::SystemTime::now();
    let ans1 = var1(&v);
    let t1 = time::SystemTime::now().duration_since(t1).unwrap().as_micros();

    let t2 = time::SystemTime::now();
    let ans2 = var2(&v);
    let t2 = time::SystemTime::now().duration_since(t2).unwrap().as_micros();

    println!("t1: {}", t1);
    println!("t2: {}", t2);
    println!("ans1: {}", ans1);
    println!("ans2: {}", ans2);

}

// EMIT_MIR var.var1.Vectorize.before.mir
// EMIT_MIR var.var1.Vectorize.after.mir
#[vectorization]
fn var1(arr: &[f32]) -> f32 {
    let mut sq_sum = 0.;
    let mut sum = 0.;
    let len = arr.len() as f32;
    for i in arr {
        sum += i;
        sq_sum += i * i;
    }
    let ave = sum / len;
    (sq_sum /  len - ave * ave).sqrt()
}

fn var2(arr: &[f32]) -> f32 {
    let mut sq_sum = 0.;
    let mut sum = 0.;
    let len = arr.len() as f32;
    for i in arr {
        sum += i;
        sq_sum += i * i;
    }
    let ave = sum / len;
    (sq_sum /  len - ave * ave).sqrt()
}
