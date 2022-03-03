#![feature(platform_intrinsics)]
#![feature(repr_simd)]
mod demo;
mod loop_simd;
mod iter_simd;
mod hex_encode;
mod var;

fn main() {
    var::use_var();
}

