use std::borrow::Cow;
use std::ops::{Deref, DerefMut};

use rayon::prelude::*;

use crate::utility::my_log;
use prime_field::FieldElement;

const MAX_ORDER: usize = 28;

#[derive(Default)]
pub struct ScratchPad {
    pub dst: [Vec<FieldElement>; 3],
    pub twiddle_factor: Vec<FieldElement>,
    pub inv_twiddle_factor: Vec<FieldElement>,
    pub twiddle_factor_size: usize,
}

impl ScratchPad {
    pub fn from_order(order: usize) -> Self {
        let dst = [
            Vec::with_capacity(order),
            Vec::with_capacity(order),
            Vec::with_capacity(order),
        ];

        let mut twiddle_factor = Vec::with_capacity(order);
        let mut inv_twiddle_factor = Vec::with_capacity(order);

        let twiddle_factor_size = order;

        let rou =
            FieldElement::get_root_of_unity(my_log(order).expect("Log order not power of two"))
                .expect("Log order too high");
        let inv_rou = rou.inverse();

        twiddle_factor.push(FieldElement::real_one());
        inv_twiddle_factor.push(FieldElement::real_one());

        let mut prev_twiddle_factor = twiddle_factor[0];
        let mut prev_inv_twiddle_factor = inv_twiddle_factor[0];
        for _ in 1..order {
            prev_twiddle_factor = rou * prev_twiddle_factor;
            prev_inv_twiddle_factor = inv_rou * prev_inv_twiddle_factor;

            twiddle_factor.push(prev_twiddle_factor);
            inv_twiddle_factor.push(prev_inv_twiddle_factor);
        }

        ScratchPad {
            dst,
            twiddle_factor,
            inv_twiddle_factor,
            twiddle_factor_size,
        }
    }

    pub fn delete(&mut self) {
        std::mem::take(&mut self.dst[0]);
        std::mem::take(&mut self.dst[1]);
        std::mem::take(&mut self.twiddle_factor);
    }
}

struct UnsafeSendSyncRawPtr<T>(*mut T);
unsafe impl<T> Sync for UnsafeSendSyncRawPtr<T> {}
unsafe impl<T> Send for UnsafeSendSyncRawPtr<T> {}

impl<T> Deref for UnsafeSendSyncRawPtr<T> {
    type Target = *mut T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for UnsafeSendSyncRawPtr<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

pub fn fast_fourier_transform(
    dst: &mut [Vec<FieldElement>; 3],
    twiddle_factor: &mut [FieldElement],
    twiddle_factor_size: &mut usize,
    coefficients: &[FieldElement],
    coefficient_len: usize,
    order: usize,
    root_of_unity: FieldElement,
    result: &mut [FieldElement],
) {
    let mut rot_mul: [FieldElement; MAX_ORDER] = [FieldElement::default(); MAX_ORDER];

    let mut log_order: Option<usize> = None;
    rot_mul[0] = root_of_unity;

    for i in 0..MAX_ORDER {
        if i > 0 {
            rot_mul[i] = rot_mul[i - 1] * rot_mul[i - 1];
        }

        if (1usize << i) == order {
            log_order = Some(i);
        }
    }

    let mut log_coefficient: Option<usize> = None;
    for i in 0..MAX_ORDER {
        if (1usize << i) == coefficient_len {
            log_coefficient = Some(i);
        }
    }

    assert!(log_order.is_some());
    assert!(log_coefficient.is_some());
    let log_order = log_order.unwrap();
    let log_coefficient = log_coefficient.unwrap();

    assert!(rot_mul[log_order] == FieldElement::real_one());
    assert!(log_coefficient <= log_order);

    let blk_sz = order / coefficient_len;

    let dst_raw = [
        UnsafeSendSyncRawPtr(&dst[0] as *const _ as *mut Vec<FieldElement>),
        UnsafeSendSyncRawPtr(&dst[1] as *const _ as *mut Vec<FieldElement>),
        UnsafeSendSyncRawPtr(&dst[2] as *const _ as *mut Vec<FieldElement>),
    ];

    (0..blk_sz).into_par_iter().for_each(|j| {
        for (i, coefficient) in coefficients
            .iter()
            .copied()
            .enumerate()
            .take(coefficient_len)
        {
            let dst_cur = &dst_raw[log_coefficient & 1];

            // Safety:
            // Different threads will all access the same dst[log_coefficient & 1] field element vec,
            // but they access disjoint indices within the vec
            let dst = unsafe { &mut *(**dst_cur).cast::<Vec<FieldElement>>() };
            dst[(j << log_coefficient) | i] = coefficient;
        }
    });

    {
        let twiddle_size = *twiddle_factor_size;
        for dep in (log_coefficient - 1)..=0 {
            let blk_size = 1 << (log_order - dep);
            let half_blk_size = blk_size >> 1;
            let cur = dep & 1;
            let pre = cur ^ 1;

            assert!(cur != pre);

            let mut cur_ptr_lock = &dst[cur];
            let mut pre_ptr_lock = &dst[pre];

            let cur_ptr_raw =
                UnsafeSendSyncRawPtr(&mut cur_ptr_lock as *const _ as *mut Vec<FieldElement>);
            let pre_ptr_raw =
                UnsafeSendSyncRawPtr(&mut pre_ptr_lock as *const _ as *mut Vec<FieldElement>);

            let gap = (twiddle_size / order) * (1 << dep);
            assert!(twiddle_size % order == 0);
            {
                (0..(blk_size / 2)).into_par_iter().for_each(|k| {
                    // Safety:
                    // Different threads will all access the same cur_ptr and pre_ptr field element vecs,
                    // but they access disjoint indices within the vec so parallel access is okay
                    let cur_ptr = unsafe { &mut *(*cur_ptr_raw).cast::<Vec<FieldElement>>() };
                    let pre_ptr = unsafe { &mut *(*pre_ptr_raw).cast::<Vec<FieldElement>>() };

                    let double_k = k & (half_blk_size - 1);
                    let x = twiddle_factor[k * gap];
                    for j in 0..(1 << dep) {
                        let l_value = pre_ptr[(double_k << (dep + 1)) | j];
                        let r_value = x * pre_ptr[(double_k << (dep + 1) | (1 << dep)) | j];

                        cur_ptr[(k << dep) | j] = l_value + r_value;
                        cur_ptr[((k + blk_size / 2) << dep) | j] = l_value - r_value;
                    }
                });
            }
        }
    }

    // result[..order].copy_from_slice(&DST[0].read().unwrap()[..order]);
}

pub fn inverse_fast_fourier_transform(
    scratch_pad: &mut ScratchPad,
    evaluations: &[FieldElement],
    mut coefficient_len: usize,
    mut order: usize,
    root_of_unity: FieldElement,
    dst: &mut [FieldElement],
) {
    if coefficient_len > order {
        eprintln!("Got insufficient number {} of evaluations for inverse fast fourier transform. Creating polynomial of order {} instead.", coefficient_len, order);
        coefficient_len = order;
    }

    let sub_eval: Cow<[FieldElement]> = {
        if coefficient_len != order {
            let mut sub_eval = Vec::with_capacity(coefficient_len);

            for i in 0..coefficient_len {
                sub_eval[i] = evaluations[i * (order / coefficient_len)];
            }

            Cow::Owned(sub_eval)
        } else {
            Cow::Borrowed(evaluations)
        }
    };

    let mut new_rou = FieldElement::real_one();
    for _ in 0..(order / coefficient_len) {
        new_rou = new_rou * root_of_unity;
    }
    order = coefficient_len;

    let mut inv_rou = FieldElement::real_one();
    let mut tmp = new_rou;

    let mut log_order: Option<usize> = None;
    for i in 0..MAX_ORDER {
        if (1usize << i) == order {
            log_order = Some(i);
            break;
        }
    }

    let mut log_coefficient: Option<usize> = None;
    for i in 0..MAX_ORDER {
        if (1usize << i) == coefficient_len {
            log_coefficient = Some(i);
            break;
        }
    }

    assert!(log_order.is_some());
    assert!(log_coefficient.is_some());

    let log_order = log_order.unwrap();

    for _ in 0..log_order {
        inv_rou = inv_rou * tmp;
        tmp = tmp * tmp;
    }
    assert!(inv_rou * inv_rou == FieldElement::real_one());

    // let mut inv_twiddle_factor = INV_TWIDDLE_FACTOR.write().unwrap();

    // fast_fourier_transform(
    //     &sub_eval[..],
    //     order,
    //     coefficient_len,
    //     inv_rou,
    //     dst,
    //     &mut inv_twiddle_factor.deref_mut()[..],
    // );

    // let inv_n = FieldElement::from_real(order.try_into().unwrap()).inverse();
    // assert!(inv_n * FieldElement::from_real(order.try_into().unwrap()) == FieldElement::real_one());

    // dst.par_iter_mut().take(coefficient_len).for_each(|item| {
    //     *item = *item * inv_n;
    // });
}
