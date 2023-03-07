#[derive(Debug)]
#[non_exhaustive]
pub enum PrimeFieldError {
    BincodeError(bincode::Error),
}

impl From<bincode::Error> for PrimeFieldError {
    fn from(err: bincode::Error) -> Self {
        Self::BincodeError(err)
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum RootOfUnityError {
    LogOrderTooHigh,
}
