//! **outils** is a graph and tree data structure library. It provides utilities which at the
//! time of writing were not available through other crates.
//!
//! As of this version of **outils**, those utilities are:
//!
//! **Fully dynamic connectivity** for general graphs: A dynamic graph data structure is able to
//! answer queries as to whether two vertices are connected in a graph through a path of edges.
//! In this context, _fully dynamic_ means that the graph can be updated by insertions or
//! deletions of edges between queries (see also [Dynamic Connectivity][1]).
//!
//! - [`DynamicGraph`][2]: Deterministic dynamic connectivity with query cost O(log(n)) and update
//! costs of O(log^2 (n)). The structure also supports vertex weights, dynamically maintaining the
//! total weight of connected components.
//!
//! **Balanced binary search trees**: A [balanced binary search tree][3] organizes search keys and
//! their associated payload in a way such that the resulting binary tree has a minimal height,
//! given the number of items stored, resulting in query and update costs of O(log(n)). This library
//! uses [AA trees][4], an abstraction of red-black trees, for balancing the trees after updates.
//!
//!  - [`AaTree`][5]: An iterative AA tree implementation using [arena allocation][6]. For most use
//! cases, it is recommended to simply use the [`BTreeMap`][7] provided by the standard library, as
//! it is considerably faster (appr. 50%). However, if information on parent and child relations
//! between tree nodes, or custom traversal of the tree as such, are needed, `AaTree` has an advantage
//! over `BTreeMap`.
//!
//!  - [`WeightedAaTree`][8]: This is similar to `AaTree`. However, in addition to the actual
//! payload, node weights can be stored and tree subweights are maintained.
//!
//! **Balanced binary forests**: A balanced binary forest is a forest of [balanced binary trees][3].
//! In contrast to the tree data structures above, the order of the payload is not determined by
//! associated search keys but by the relations of the nodes to each other: the in-order traversal
//! of a forest tree alone represents the order of its nodes. Forest trees can be concatenated or
//! split in order to manage those sequences. Parent and child relations are available, facilitating
//! analysis of the represented sequences.
//!
//!  - [`AaForest`][9]: A forest of trees balanced by the [AA tree][4] algorithm. Concatenation and
//! separation do not require a reorganisation of the tree according to search keys - only
//! rebalancing will take place, the order of the sequence being the responsibility of the user.
//! The implementation is based on [arena allocation][6], and tree queries and updates are conducted
//! iteratively, as in the corresponding AA tree structures above.
//!
//!  - [`WeightedAaForest`][10]: This is similar to `AaForest`. However, in addition to the actual
//! payload, a node weight can be stored and tree subweights are maintained.
//!
//! [1]: https://en.wikipedia.org/wiki/Dynamic_connectivity
//! [2]: ./graph/dynconn/hdt/struct.DynamicGraph.html
//! [3]: https://en.wikipedia.org/wiki/Self-balancing_binary_search_tree
//! [4]: https://en.wikipedia.org/wiki/AA_tree
//! [5]: ./tree/bst/aatree/struct.AaTree.html
//! [6]: https://en.wikipedia.org/wiki/Region-based_memory_management
//! [7]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html
//! [8]: ./tree/bst/waatree/struct.WeightedAaTree.html
//! [9]: ./tree/bst/aaforest/struct.AaForest.html
//! [10]: ./tree/bst/waaforest/struct.WeightedAaForest.html

#![warn(missing_docs)]

extern crate core;
extern crate rand;
extern crate slab;

pub mod tree;
pub mod graph;
pub mod types;
pub mod prelude;
