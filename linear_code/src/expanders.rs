use prime_field::FieldElement;
use std::vec::Vec;

// use the same distance parameter from brakedown
pub const target_distance: f64 = 0.07;
pub const distance_threshold: i32 = ((1.0 / target_distance) as i32) - 1;
pub const rs_rate: i32 = 2;
pub const alpha: f64 = 0.238;
pub const beta: f64 = 0.1205;
pub const r: f64 = 1.72;
pub const cn: i32 = 10;
pub const dn: i32 = 20;
pub const column_size: i32 = 128;

#[derive(Default)]
pub struct Graph {
    pub degree: i32,
    pub neighbor: Vec<Vec<i64>>,
    pub r_neighbor: Vec<Vec<i64>>,
    pub weight: Vec<Vec<FieldElement>>,
    pub r_weight: Vec<Vec<FieldElement>>,
    pub L: i64,
    pub R: i64,
}

// TODO

// pub static mut C: [Graph; 100] = [Graph::default(); 100];
// pub static mut D: [Graph; 100] = [Graph::default(); 100];

// TODO this can be something like
// this https://crates.io/crates/lazy_static or this https://github.com/matklad/once_cell

pub static mut C: Vec<Graph> = Vec::new(); // TODO this can actually be lazy_cell
pub static mut D: Vec<Graph> = Vec::new(); // TODO this can actually be lazy_cell

#[inline]
pub fn generate_random_expander(L: i64, R: i64, d: i64) -> Graph {
    let mut ret: Graph = Graph::default();
    ret.degree = i32::try_from(d).unwrap();
    ret.neighbor.truncate(L as usize);
    ret.weight.truncate(L as usize);

    ret.r_neighbor.truncate(R as usize);
    ret.r_weight.truncate(R as usize);

    for i in 0..(L as usize) {
        ret.neighbor[i].truncate(d as usize);
        ret.weight[i].truncate(d as usize);
        for j in 0..(d as usize) {
            let target: i64 = rand::random::<i64>() % R;
            // TODO
            // let weight: FieldElement = prime_field::random();
            let weight = FieldElement::default();
            ret.neighbor[i][j] = target;
            ret.r_neighbor[target as usize].push(i as i64);
            ret.r_weight[target as usize].push(weight);
            ret.weight[i][j] = weight;
        }
    }

    ret.L = L;
    ret.R = R;
    ret
}

#[inline]
pub unsafe fn expander_init(n: i64, dep: Option<i32>) -> i64 {
    // random Graph
    if n <= distance_threshold as i64 {
        n
    } else {
        let mut dep_ = dep.unwrap_or(0i32);
        C[dep_ as usize] = generate_random_expander(n, ((alpha * (n as f64)) as i64), cn as i64);
        let L: i64 = expander_init(((alpha * (n as f64)) as i64), Some(dep_ + 1i32));
        D[dep_ as usize] = generate_random_expander(
            L,
            (((n as f64) * (r - 1f64) - (L as f64)) as i64),
            dn as i64,
        );
        n + L + (((n as f64) * (r - 1.0) - (L as f64)) as i64)
    }
}
