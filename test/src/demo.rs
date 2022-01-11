

pub fn use_demo() {
    let mut src = [0; 75264];
    let mut integral = [0; 75264].to_vec();
    get_power_integral_image(&mut src, &mut integral, 224, 224);
    println!("{}", integral[0]);
}

fn get_power_integral_image(src:&mut [u8; 75264], integral:&mut Vec<u32>, height: usize, width: usize)
{
    for y in 0..height {
        let offset = y * width;
        let offset_l = y * (width + 1) + 1;
        let offset_d = (y + 1) * (width + 1) + 1;
        let mut sum:u32 = 0;
        for x in 0..width {
            let val = src[offset + x] as u32;
            sum = sum + val * val;
            integral[offset_d + x] = integral[offset_l + x] + sum;
        }
    }
}