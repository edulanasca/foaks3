use prime_field::FieldElement;
use std::mem::size_of_val;
use std::ptr::copy_nonoverlapping;
use std::vec::Vec;

use crate::my_hash::{my_hash, HashDigest};

pub static mut size_after_padding: usize = 0;

pub unsafe fn hash_single_field_element(x: FieldElement) -> HashDigest {
    let mut data = [HashDigest::default(); 2];
    copy_nonoverlapping(
        std::ptr::addr_of!(x) as *const i128,
        std::ptr::addr_of_mut!(data[0].h0),
        size_of_val(&x),
    );
    assert_eq!(size_of_val(&x), size_of_val(&data[0].h0));
    my_hash(data)
}

pub unsafe fn hash_double_field_element_merkle_damgard(
    x: FieldElement,
    y: FieldElement,
    prev_hash: HashDigest,
) -> HashDigest {
    let mut data = [HashDigest::default(); 2];
    data[0] = prev_hash;
    let mut element = [x, y];
    copy_nonoverlapping(
        std::ptr::addr_of!(element) as *const HashDigest,
        std::ptr::addr_of_mut!(data[1]),
        size_of_val(&data[1]),
    );
    assert_eq!(size_of_val(&data[1]), size_of_val(&element));
    my_hash(data)
}

pub unsafe fn create_tree(
    src_data: Vec<HashDigest>,
    element_num: usize,
    dst: &mut Vec<HashDigest>,
    element_size_: Option<usize>,
    alloc_required_: Option<bool>,
) {
    // init
    // NOTE: actually the element size is the size_of::<HashDigest>
    // NOTE: src_data.len() == element_num = true
    let element_size = element_size_.unwrap_or(256 / 8);
    let alloc_required = alloc_required_.unwrap_or(false);
    size_after_padding = 1;
    while size_after_padding < element_num {
        size_after_padding *= 2;
    }
    if alloc_required {
        *dst = vec![HashDigest::default(); size_after_padding * 2];
        /*
        dst_ptr = (__hhash_digest*)malloc(size_after_padding * 2 * element_size);
        if(dst_ptr == NULL)
        {
            printf("Merkle Tree Bad Alloc\n");
            abort();
        }
        */
    }
    let mut start_idx = size_after_padding;
    let mut current_lvl_size = size_after_padding;
    // TODO: parallel
    for i in (current_lvl_size - 1)..=0 {
        let mut data = [HashDigest::default(); 2];
        if i < element_num {
            dst[i + start_idx] = src_data[i];
        } else {
            data = [HashDigest::default(); 2];
            // my_hash(data, &mut dst[i + start_idx]);
            dst[i + start_idx] = my_hash(data);
        }
    }
    current_lvl_size /= 2;
    start_idx -= current_lvl_size;
    while current_lvl_size >= 1 {
        // TODO: parallel
        for i in 0..current_lvl_size {
            let mut data = [HashDigest::default(); 2];
            data[0] = dst[start_idx + current_lvl_size + i * 2];
            data[1] = dst[start_idx + current_lvl_size + i * 2 + 1];
            // my_hash(data, &mut dst[start_idx + i]);
            dst[start_idx + i] = my_hash(data);
        }
        current_lvl_size /= 2;
        start_idx -= current_lvl_size;
    }
}

pub fn verify_claim(
    root_hash: HashDigest,
    tree: Vec<HashDigest>,
    leaf_hash: &mut HashDigest,
    pos_element_arr: usize,
    N: usize,
    visited: &mut Vec<bool>,
    proof_size: &mut usize,
) -> bool {
    // check N is power of 2
    assert_eq!(((N as i64) & -(N as i64)), N as i64);
    let mut pos_element = pos_element_arr + N;
    let mut data = [HashDigest::default(); 2];
    while pos_element != 1 {
        let pos_1 = pos_element & 1;
        let pos_2 = pos_element ^ 1;
        data[pos_1] = *leaf_hash;
        data[pos_1 ^ 1] = tree[pos_2];
        if !visited[pos_2] {
            visited[pos_2] = true;
            *proof_size += size_of_val(&leaf_hash);
        }
        *leaf_hash = my_hash(data);
        // my_hash(data, leaf_hash);
        pos_element /= 2;
    }
    root_hash == *leaf_hash
}
