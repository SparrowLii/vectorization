#![feature(platform_intrinsics, repr_simd)]

extern "platform-intrinsic" {
    pub fn simd_mul<T>(x: T, y: T) -> T;
    pub fn simd_add<T>(x: T, y: T) -> T;
    pub fn simd_reduce_add_unordered<T, U>(x: T) -> U;
}


pub fn use_var() {
    use std::time;
    const LEN: usize = 51200;
    let mut v: [f32; LEN] = [0.; LEN];
    for i in 0..LEN {
        v[i] = ((i * i - i) % 100) as f32;
    }

    let t2 = time::SystemTime::now();
    let ans2 = var2(&v);
    let t2 = time::SystemTime::now().duration_since(t2).unwrap().as_micros();

    let t1 = time::SystemTime::now();
    let ans1 = var1(&v);
    let t1 = time::SystemTime::now().duration_since(t1).unwrap().as_micros();



    //assert_eq!(ans1, ans2);

    println!("t1: {}", t1);
    println!("t2: {}", t2);
    println!("ans1: {}", ans1);
    println!("ans2: {}", ans2);

}

const SIMD_LEN: usize = 64;
#[repr(simd)]
#[derive(Copy, Clone)]
pub struct SIMD([f32; SIMD_LEN]);

fn var1(arr: &[f32]) -> f32 {
    let mut sq_sum = SIMD([0.; SIMD_LEN]);
    let mut sum = SIMD([0.; SIMD_LEN]);
    let len = arr.len() as f32;
    for i in 0..arr.len() / SIMD_LEN {
        let offset = i * SIMD_LEN;
        unsafe {
            let temp: SIMD = std::ptr::read_unaligned(&arr[offset] as *const f32 as *const SIMD);
            sum = simd_add(sum, temp);
            sq_sum = simd_add(sq_sum, simd_mul(temp, temp));
        }
    }
    let sq_sum: f32 = unsafe{
        simd_reduce_add_unordered(sq_sum)
    };
    let sum: f32 = unsafe{
        simd_reduce_add_unordered(sum)
    };
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





