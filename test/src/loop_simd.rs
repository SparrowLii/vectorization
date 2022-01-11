

use std::time;

extern "platform-intrinsic" {
    pub fn simd_fsqrt<T>(a: T) -> T;
    pub fn simd_add<T>(x: T, y: T) -> T;
    pub fn simd_reduce_add_unordered<T, U>(x: T) -> U;
}

pub fn use_loop() {
    let t1 = time::SystemTime::now();
    let f1 = func1(1280005);
    let t1 = time::SystemTime::now()
        .duration_since(t1)
        .unwrap()
        .as_micros();

    let t2 = time::SystemTime::now();
    let f2 = func2(1280005);
    let t2 = time::SystemTime::now()
        .duration_since(t2)
        .unwrap()
        .as_micros();

    println!("t1:{}", t1);
    println!("t2:{}", t2);
    assert!((f1 - f2) / f2 < 0.001);
}

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
    #[cfg(target_arch = "x86_64")]
    const SIMD_LEN: usize = 32;
    #[cfg(target_arch = "aarch64")]
    const SIMD_LEN: usize = 8;
    #[repr(simd)]
    #[derive(Copy, Clone)]
    pub struct MySIMD<T>([T; SIMD_LEN]);

    let mut index = 0;
    let mut sum: MySIMD<f32> = MySIMD([0.; SIMD_LEN]);
    let mut temp: MySIMD<f32> = MySIMD([0.; SIMD_LEN]);
    let mut ans = 0.;
    let mut inner;
    unsafe {
        'outer: loop {
            inner = 0;
            loop {
                if inner >= SIMD_LEN {
                    break;
                }
                if index >= len {
                    break 'outer;
                }
                temp.0[inner] = index as f32;
                index += 1;
                inner += 1;
            }
            sum = simd_add(sum, simd_fsqrt(temp));
        }
        if index >= SIMD_LEN {
            ans += simd_reduce_add_unordered::<_, f32>(sum);
        }
        loop {
            if inner <= 0 {
                break;
            }
            inner -= 1;
            ans += (temp.0[inner]).sqrt();
        }
    }
    ans
}
