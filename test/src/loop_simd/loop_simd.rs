#![feature(rustc_attrs)]

pub fn main() {
    let sum1 = func1(2048);
    let sum2 = func2(2048);
    assert_eq!(sum1, sum2);
    println!("sum: {}", sum1);
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

