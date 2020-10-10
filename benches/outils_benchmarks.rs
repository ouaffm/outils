#[macro_use]
extern crate bencher;
#[macro_use]
extern crate lazy_static;

use rand;

use bencher::Bencher;
use outils::graph::dynconn::{DynamicConnectivity, DynamicWeightedComponent};
use outils::graph::dynconn::hdt::DynamicGraph;
use outils::tree::bst::aaforest::AaForest;
use outils::tree::bst::aatree::AaTree;
use outils::tree::bst::BalancedBinaryForest;
use outils::tree::bst::BinarySearchTree;
use outils::tree::bst::waaforest::WeightedAaForest;
use outils::tree::WeightedTree;
use outils::types::{EmptyWeight, VertexIndex};
use rand::Rng;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::fmt::Display;
use std::ops::{Add, AddAssign};

lazy_static! {
    static ref BIG_INSERT_DELETE_SIZE: usize = 10_000;
    static ref BITBOARD_WEIGHT_LENGTH: usize = 384;
    static ref BIG_INSERT_DELETE_DATE: Vec<usize> = {
        let mut list = Vec::with_capacity(*BIG_INSERT_DELETE_SIZE);
        let mut rng = rand::thread_rng();
        for _ in 0..*BIG_INSERT_DELETE_SIZE {
            list.push(rng.gen::<usize>());
        }
        list
    };
    static ref BITBOARD_WEIGHTS: Vec<BitboardWeight> = {
        let mut list = Vec::with_capacity(*BITBOARD_WEIGHT_LENGTH);
        let mut rng = rand::thread_rng();
        for _ in 0..*BITBOARD_WEIGHT_LENGTH {
            list.push(BitboardWeight {
                blocks: [
                    rng.gen::<u64>(),
                    rng.gen::<u64>(),
                    rng.gen::<u64>(),
                    rng.gen::<u64>(),
                    rng.gen::<u64>(),
                    rng.gen::<u64>(),
                ],
            });
        }
        list
    };
}

#[derive(Default, Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct UsizeBoolWeight {
    weight: usize,
    flag: bool,
}

impl Display for UsizeBoolWeight {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}, {})", self.weight, self.flag)
    }
}

impl Add for UsizeBoolWeight {
    type Output = UsizeBoolWeight;

    fn add(self, other: UsizeBoolWeight) -> UsizeBoolWeight {
        UsizeBoolWeight {
            weight: self.weight + other.weight,
            flag: self.flag | other.flag,
        }
    }
}

impl AddAssign for UsizeBoolWeight {
    fn add_assign(&mut self, other: UsizeBoolWeight) {
        *self = UsizeBoolWeight {
            weight: self.weight + other.weight,
            flag: self.flag | other.flag,
        }
    }
}

#[derive(Default, Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct Usize2Weight {
    weight: [usize; 2],
}

impl Display for Usize2Weight {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}, {})", self.weight[0], self.weight[1])
    }
}

impl Add for Usize2Weight {
    type Output = Usize2Weight;

    fn add(self, other: Usize2Weight) -> Usize2Weight {
        Usize2Weight {
            weight: [
                self.weight[0] + other.weight[0],
                self.weight[1] + other.weight[1],
            ],
        }
    }
}

impl AddAssign for Usize2Weight {
    fn add_assign(&mut self, other: Usize2Weight) {
        *self = Usize2Weight {
            weight: [
                self.weight[0] + other.weight[0],
                self.weight[1] + other.weight[1],
            ],
        }
    }
}

#[derive(Default, Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct BitboardWeight {
    blocks: [u64; 6],
}

#[derive(Default, Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct CombinedWeight {
    weight1: UsizeBoolWeight,
    weight2: Usize2Weight,
}

impl Display for CombinedWeight {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({} {} {}, {})",
            self.weight1.weight, self.weight1.flag, self.weight2.weight[0], self.weight2.weight[1]
        )
    }
}

impl Add for BitboardWeight {
    type Output = BitboardWeight;

    fn add(self, other: BitboardWeight) -> BitboardWeight {
        BitboardWeight {
            blocks: [
                self.blocks[0] | other.blocks[0],
                self.blocks[1] | other.blocks[1],
                self.blocks[2] | other.blocks[2],
                self.blocks[3] | other.blocks[3],
                self.blocks[4] | other.blocks[4],
                self.blocks[5] | other.blocks[5],
            ],
        }
    }
}

impl AddAssign for BitboardWeight {
    fn add_assign(&mut self, other: BitboardWeight) {
        *self = BitboardWeight {
            blocks: [
                self.blocks[0] | other.blocks[0],
                self.blocks[1] | other.blocks[1],
                self.blocks[2] | other.blocks[2],
                self.blocks[3] | other.blocks[3],
                self.blocks[4] | other.blocks[4],
                self.blocks[5] | other.blocks[5],
            ],
        }
    }
}

impl Display for BitboardWeight {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({} {} {} {} {} {})",
            self.blocks[0],
            self.blocks[1],
            self.blocks[2],
            self.blocks[3],
            self.blocks[4],
            self.blocks[5]
        )
    }
}

impl Add for CombinedWeight {
    type Output = CombinedWeight;

    fn add(self, other: CombinedWeight) -> CombinedWeight {
        CombinedWeight {
            weight1: self.weight1 + other.weight1,
            weight2: self.weight2 + other.weight2,
        }
    }
}

impl AddAssign for CombinedWeight {
    fn add_assign(&mut self, other: CombinedWeight) {
        *self = CombinedWeight {
            weight1: self.weight1 + other.weight1,
            weight2: self.weight2 + other.weight2,
        }
    }
}

fn aatree_big_random_insert_delete(bench: &mut Bencher) {
    let mut tree: AaTree<usize, _> = AaTree::new(*BIG_INSERT_DELETE_SIZE);
    bench.iter(|| {
        for x in 0..*BIG_INSERT_DELETE_SIZE {
            let key = BIG_INSERT_DELETE_DATE[x];
            tree.insert(key, " ");
        }
        for x in 0..*BIG_INSERT_DELETE_SIZE {
            let key = BIG_INSERT_DELETE_DATE[x];
            tree.remove(key);
        }
    })
}

fn hashmap_big_random_insert_delete(bench: &mut Bencher) {
    let mut tree: HashMap<usize, _> = HashMap::with_capacity(*BIG_INSERT_DELETE_SIZE);
    bench.iter(|| {
        for x in 0..*BIG_INSERT_DELETE_SIZE {
            let key = BIG_INSERT_DELETE_DATE[x];
            tree.insert(key, " ");
        }
        for x in 0..*BIG_INSERT_DELETE_SIZE {
            let key = BIG_INSERT_DELETE_DATE[x];
            tree.remove(&key);
        }
    })
}

fn btreemap_big_random_insert_delete(bench: &mut Bencher) {
    let mut tree: BTreeMap<usize, _> = BTreeMap::new();
    bench.iter(|| {
        for x in 0..*BIG_INSERT_DELETE_SIZE {
            let key = BIG_INSERT_DELETE_DATE[x];
            tree.insert(key, " ");
        }
        for x in 0..*BIG_INSERT_DELETE_SIZE {
            let key = BIG_INSERT_DELETE_DATE[x];
            tree.remove(&key);
        }
    })
}

fn waaforest_big_random_append(bench: &mut Bencher) {
    let mut tree: WeightedAaForest<usize> = WeightedAaForest::new(*BIG_INSERT_DELETE_SIZE);
    let mut root = tree.insert(0);
    bench.iter(|| {
        for x in 0..*BIG_INSERT_DELETE_SIZE {
            let node = tree.insert(BIG_INSERT_DELETE_DATE[x]);
            tree.set_weight(node, 1);
            root = tree.append(root, node).map_or(root, |r| r);
        }
    })
}

fn aaforest_big_random_append(bench: &mut Bencher) {
    let mut tree: AaForest<usize> = AaForest::new(*BIG_INSERT_DELETE_SIZE);
    let mut root = tree.insert(0);
    bench.iter(|| {
        for x in 0..*BIG_INSERT_DELETE_SIZE {
            let node = tree.insert(BIG_INSERT_DELETE_DATE[x]);
            root = tree.append(root, node).map_or(root, |r| r);
        }
    })
}

fn waaforest_big_random_append_empty_weight(bench: &mut Bencher) {
    let mut tree: WeightedAaForest<usize, EmptyWeight> =
        WeightedAaForest::new(*BIG_INSERT_DELETE_SIZE);
    let mut root = tree.insert(0);
    bench.iter(|| {
        for x in 0..*BIG_INSERT_DELETE_SIZE {
            let node = tree.insert(BIG_INSERT_DELETE_DATE[x]);
            root = tree.append(root, node).map_or(root, |r| r);
        }
    })
}

fn waaforest_big_random_append_usize_bool_weight(bench: &mut Bencher) {
    let mut tree: WeightedAaForest<usize, UsizeBoolWeight> =
        WeightedAaForest::new(*BIG_INSERT_DELETE_SIZE);
    let mut root = tree.insert(0);
    bench.iter(|| {
        for x in 0..*BIG_INSERT_DELETE_SIZE {
            let node = tree.insert(BIG_INSERT_DELETE_DATE[x]);
            tree.set_weight(
                node,
                UsizeBoolWeight {
                    weight: 1,
                    flag: x % 2 == 0,
                },
            );
            root = tree.append(root, node).map_or(root, |r| r);
        }
    })
}

fn waaforest_big_random_append_usize_2_weight(bench: &mut Bencher) {
    let mut tree: WeightedAaForest<usize, Usize2Weight> =
        WeightedAaForest::new(*BIG_INSERT_DELETE_SIZE);
    let mut root = tree.insert(0);
    bench.iter(|| {
        for x in 0..*BIG_INSERT_DELETE_SIZE {
            let node = tree.insert(BIG_INSERT_DELETE_DATE[x]);
            tree.set_weight(node, Usize2Weight { weight: [x, x + 1] });
            root = tree.append(root, node).map_or(root, |r| r);
        }
    })
}

fn waaforest_big_random_append_combined_weight(bench: &mut Bencher) {
    let mut tree: WeightedAaForest<usize, CombinedWeight> =
        WeightedAaForest::new(*BIG_INSERT_DELETE_SIZE);
    let mut root = tree.insert(0);
    bench.iter(|| {
        for x in 0..*BIG_INSERT_DELETE_SIZE {
            let node = tree.insert(BIG_INSERT_DELETE_DATE[x]);
            tree.set_weight(
                node,
                CombinedWeight {
                    weight1: UsizeBoolWeight {
                        weight: 1,
                        flag: x % 2 == 0,
                    },
                    weight2: Usize2Weight { weight: [x, x + 1] },
                },
            );
            root = tree.append(root, node).map_or(root, |r| r);
        }
    })
}

fn waaforest_big_random_append_bitboard_weight(bench: &mut Bencher) {
    let mut tree: WeightedAaForest<usize, BitboardWeight> =
        WeightedAaForest::new(*BIG_INSERT_DELETE_SIZE);
    let mut root = tree.insert(0);
    bench.iter(|| {
        for x in 0..*BIG_INSERT_DELETE_SIZE {
            let node = tree.insert(BIG_INSERT_DELETE_DATE[x]);
            tree.set_weight(node, BITBOARD_WEIGHTS[x % *BITBOARD_WEIGHT_LENGTH]);
            root = tree.append(root, node).map_or(root, |r| r);
        }
    })
}

fn dynconn_big_insert_delete(bench: &mut Bencher) {
    let mut dg: DynamicGraph<EmptyWeight> = DynamicGraph::new(100, 100);
    let mut edges = Vec::with_capacity(10_000);

    bench.iter(|| {
        for i in 0..100 {
            for j in 0..100 {
                dg.insert_edge(VertexIndex(i), VertexIndex(j))
                    .map(|e| edges.push(e));
            }
        }
        while let Some(e) = edges.pop() {
            dg.delete_edge(e);
        }
    })
}

fn dynconn_big_insert_delete_ext_weight(bench: &mut Bencher) {
    let mut dg: DynamicGraph<BitboardWeight> = DynamicGraph::new(100, 100);
    for i in 0..100 {
        dg.set_vertex_weight(VertexIndex(i), BITBOARD_WEIGHTS[i]);
    }
    let mut edges = Vec::with_capacity(10_000);

    bench.iter(|| {
        for i in 0..100 {
            for j in 0..100 {
                dg.insert_edge(VertexIndex(i), VertexIndex(j))
                    .map(|e| edges.push(e));
            }
        }
        while let Some(e) = edges.pop() {
            dg.delete_edge(e);
        }
    })
}

benchmark_group!(
    benches,
    aatree_big_random_insert_delete,
    btreemap_big_random_insert_delete,
    hashmap_big_random_insert_delete,
    aaforest_big_random_append,
    waaforest_big_random_append,
    waaforest_big_random_append_empty_weight,
    waaforest_big_random_append_usize_bool_weight,
    waaforest_big_random_append_usize_2_weight,
    waaforest_big_random_append_combined_weight,
    waaforest_big_random_append_bitboard_weight,
    dynconn_big_insert_delete,
    dynconn_big_insert_delete_ext_weight
);
benchmark_main!(benches);
