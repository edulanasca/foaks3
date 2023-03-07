#[derive(Debug)]
pub enum Log2Error {
    NotPowerOfTwo,
}

pub fn my_log(x: usize) -> Result<usize, Log2Error> {
    for i in 0..64 {
        if 1usize << i == x {
            return Ok(i);
        }
    }
    Err(Log2Error::NotPowerOfTwo)
}

pub fn min(x: i32, y: i32) -> i32 {
    if x > y {
        y
    } else {
        x
    }
}

pub fn max(x: i32, y: i32) -> i32 {
    if x > y {
        x
    } else {
        y
    }
}
