extern "platform-intrinsic" {
    pub fn simd_mul<T>(x: T, y: T) -> T;
    pub fn simd_add<T>(x: T, y: T) -> T;
}

pub fn use_iter() {
    let mut src: [u8; 224] = [0; 224];
    let mut src2: [u32; 224] = [0; 224];
    let mut val = src.map(|v| v as u32).to_vec();
    func1(&mut src, &src2, &mut val);
    //func2(&src, &src2, &mut val);
    println!("{}", val[0]);
}

fn func1(src: &[u8], src2: &[u32], val: &mut [u32])
{
    let mut sum = 0;
    for x in 0..src.len() {
        let v = src[x] as u32;
        sum += v * v;
        val[x] = src2[x] + sum;
    }
}

/*fn func2(src:&[u8], src2: &[u32], val: &mut [u32]) {
    let mut sum = 0;
    let mut x = 0;
    loop {
        let mut xv: [usize; 4] = [0; 4];
        let mut inner = 0;
        loop {
            if inner >= 4 {
                break
            }
            if x >= src.len() {
                break
            }
            xv[inner] = x;
            x += 1;
            inner += 1;
        }

        let v: [u8; 4] = unsafe {
            std::ptr::read_unaligned(src.as_ptr().add(xv[0]).cast())
        };

        let mut vv: [u32; 4] = [0; 4];
        inner = 0;
        loop {
            if inner >= 4 {
                break
            }
            vv[inner] = v[inner] as u32;
            inner += 1;
        }

        vv = unsafe {
            simd_mul(vv, vv)
        };

        let mut sv: [u32; 4] = [0; 4];
        inner = 0;
        loop {
            if inner >= 4 {
                break
            }
            sum += vv[inner];
            sv[inner] = sum;
            inner += 1;
        }

        let mut ssv: [u32; 4] = unsafe {
            std::ptr::read_unaligned(src2.as_ptr().add(xv[0]).cast())
        };

        ssv = unsafe {
            simd_add(ssv, sv)
        };

        unsafe {
            std::ptr::write_unaligned(val.as_mut_ptr().cast(), ssv);
        }
    }
}*/

