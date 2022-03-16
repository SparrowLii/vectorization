#![feature(rustc_attrs)]

pub fn main() {
    use std::time;

    let t2 = time::SystemTime::now();
    let sum2 = func2(2048024);
    let t2 = time::SystemTime::now().duration_since(t2).unwrap().as_micros();

    let t1 = time::SystemTime::now();
    let sum1 = func1(2048024);
    let t1 = time::SystemTime::now().duration_since(t1).unwrap().as_micros();

    println!("sum1: {}", sum1);
    println!("sum2: {}", sum2);

    println!("t1: {}", t1);
    println!("t2: {}", t2);
}

// EMIT_MIR loop_simd.func1.Vectorize.before.mir
// EMIT_MIR loop_simd.func1.Vectorize.after.mir
#[vectorization]
fn func1(len: usize) -> f32 {
    let mut index = 0;
    let mut sum: f32 = 0.;
    loop {
        if index >= len {
            break;
        }
        sum += (index as f32).sqrt();
        index += 1;
    }
    sum
}

fn func2(len: usize) -> f32 {
    let mut index = 0;
    let mut sum: f32 = 0.;
    loop {
        if index >= len {
            break;
        }
        sum += (index as f32).sqrt();
        index += 1;
    }
    sum
}
