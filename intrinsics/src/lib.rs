pub mod i256 {
    use ethnum::{i256, u256};

    pub fn srl(x: &i256, c: u32) -> i256 {
        u256::as_i256(x.as_u256() >> c)
    }

    pub fn sll(x: &i256, c: u32) -> i256 {
        u256::as_i256(x.as_u256() << c)
    }
}
