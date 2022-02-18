

use std::time;

extern "platform-intrinsic" {
    pub fn simd_fsqrt<T>(a: T) -> T;
    pub fn simd_add<T>(x: T, y: T) -> T;
    pub fn simd_reduce_add_unordered<T, U>(x: T) -> U;
}

pub fn use_loop() {
    let t1 = time::SystemTime::now();
    let f1 = func1(2048000);
    let t1 = time::SystemTime::now()
        .duration_since(t1)
        .unwrap()
        .as_micros();

    let t3 = time::SystemTime::now();
    let f3 = func3(2048000);
    let t3 = time::SystemTime::now()
        .duration_since(t3)
        .unwrap()
        .as_micros();

    let t2 = time::SystemTime::now();
    let f2 = func2(2048000);
    let t2 = time::SystemTime::now()
        .duration_since(t2)
        .unwrap()
        .as_micros();



    println!("t1:{}", t1);
    println!("t2:{}", t2);
    println!("t3:{}", t3);
    assert!((f1 - f2) / f2 < 0.001);
    assert!((f1 - f3) / f3 < 0.001);
}

#[cfg(target_arch = "x86_64")]
const SIMD_LEN: usize = 32;
#[cfg(target_arch = "aarch64")]
const SIMD_LEN: usize = 8;

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

fn func3(len: usize) -> f32 {
    #[repr(simd)]
    #[derive(Copy, Clone)]
    pub struct MySIMD<T>([T; SIMD_LEN]);

    let mut index = 0;
    let mut sum = 0.;
    // 外循环递增条件(实际中省略初始化)
    let mut temp: MySIMD<usize> = MySIMD([0; SIMD_LEN]);

    // 创建内循环条件
    let mut inner;

    // 临时SIMD变量(实际中省略初始化)
    let mut v_temp: MySIMD<f32> = MySIMD([0.; SIMD_LEN]);

    unsafe {
        // 外循环开始
        'outer: loop {

            // 内循环条件重置
            inner = 0;
            // 内循环开始
            loop {
                // 内循环跳出
                if inner >= SIMD_LEN {
                    break;
                }
                // 包含条件语句
                if index >= len {
                    break 'outer;
                }
                // 读取条件语句
                temp.0[inner] = index;

                //外循环递增
                index += 1;

                // 非SIMD操作
                v_temp.0[inner] = temp.0[inner] as f32;

                // 内循环递增
                inner += 1;
            }
            // SIMD操作
            sum += simd_reduce_add_unordered::<_, f32>(simd_fsqrt(v_temp));
        }
        // 剩余外循环
        let mut p = 0;
        loop {
            if p >= inner {
                break;
            }
            sum += (temp.0[p] as f32).sqrt();
            p += 1;
        }
    }
    sum
}

fn func2(len: usize) -> f32 {
    #[repr(simd)]
    #[derive(Copy, Clone)]
    pub struct MySIMD<T>([T; SIMD_LEN]);

    let mut index = 0;
    let mut sum = 0.;
    let mut v_sum: MySIMD<f32> = MySIMD([0.; SIMD_LEN]);
    let mut temp: MySIMD<f32> = MySIMD([0.; SIMD_LEN]);
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
            v_sum = simd_add(v_sum, simd_fsqrt(temp));
        }
        if index >= SIMD_LEN {
            sum += simd_reduce_add_unordered::<_, f32>(v_sum);
        }
        let mut p = 0;
        loop {
            if p >= inner {
                break;
            }
            sum += (temp.0[p]).sqrt();
            p += 1;
        }
    }
    sum
}
