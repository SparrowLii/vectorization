#![feature(rustc_attrs)]
pub fn main() {
    use std::time;

    let t1 = time::SystemTime::now();
    let s1 = u8_cal(2560000);
    let t1 = time::SystemTime::now().duration_since(t1).unwrap().as_micros();

    let t2 = time::SystemTime::now();
    let s2 = u8_cal_2(2560000);
    let t2 = time::SystemTime::now().duration_since(t2).unwrap().as_micros();

    assert_eq!(s1, s2);

    println!("t1: {}", t1);
    println!("t2: {}", t2);
    println!("s1: {}", s1);
    println!("s2: {}", s2);

}

// EMIT_MIR u8_cal.u8_cal.Vectorize.before.mir
// EMIT_MIR u8_cal.u8_cal.Vectorize.after.mir
#[vectorization]
fn u8_cal(len: u64) -> u8 {
    let mut ans: u8 = 0;
    for index in 0..len {
        let byte = index as u8;
        ans += (byte >> 4) & 0xf;
        ans += byte & 0xf;
    }
    ans
}

fn u8_cal_2(len: u64) -> u8 {
    let mut ans: u8 = 0;
    for index in 0..len {
        let byte = index as u8;
        ans += (byte >> 4) & 0xf;
        ans += byte & 0xf;
    }
    ans
}
