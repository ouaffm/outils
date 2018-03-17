//! **outils** is a graph and tree data structure library. It provides utilities which at the
//! time of writing were not available through other crates.
//!
//! As of this version of **outils**, those utilities are:
//!
//! **Fully dynamic connectivity** for general graphs: A dynamic graph data structure is able to
//! answer queries as to whether two vertices are connected in a graph through a path of edges.
//! In this context, _fully dynamic_ means that the graph can be updated by insertions or
//! deletions of edges between queries (see also <https://en.wikipedia.org/wiki/Dynamic_connectivity>)
//!
//! - [`DynamicGraph`](./graph/dynconn/hdt/struct.DynamicGraph.html): Deterministic
//! dynamic connectivity with query cost O(log(n)) and update costs of O(log^2 (n)). The structure
//! also supports vertex weights, dynamically maintaining the total weight of connected components.
//!
//! **Balanced binary search trees**: A balanced binary search tree organizes search keys and their
//! associated payload in a way such that the resulting binary tree has a minimal height, given the
//! number of items stored, resulting in query and update costs of O(log(n)). This library uses
//! AA trees (see <https://en.wikipedia.org/wiki/AA_tree>, an abstraction of red-black trees, for
//! balancing the trees after updates.
//!
//!  - [`AaTree`](./tree/bst/aatree/struct.AaTree.html): An iterative AA tree implementation using
//! arena allocation. For most use cases, it is recommended to simply use the
//! [`BTreeMap`](https://doc.rust-lang.org/std/collections/struct.BTreeMap.html) provided by the standard
//! library, as it is considerably faster (appr. 50%). However, if information on parent and child
//! relations between tree nodes, or custom traversal of the tree as such, are needed, `AaTree` has
//! an advantage over `BTreeMap`.
//!
//!  - [`WeightedAaTree`](./tree/bst/waatree/struct.WeightedAaTree.html): This is similar to `AaTree`.
//! However, in addition to the actual payload, node weights can be stored and tree subweights
//! are maintained.
//!
//! **Balanced binary forests**: A balanced binary forest is a forest of balanced binary trees. In
//! contrast to the tree data structures above, the order of the payload is not determined by associated
//! search keys but by the relations of the nodes to each other: the in-order traversal of a forest tree
//! alone represents the order of its nodes. Forest trees can be concatenated or split in order to manage those
//! sequences. Parent and child relations are available, facilitating analysis of the represented sequences.
//!
//!  - [`AaForest`](./tree/bst/aaforest/struct.AaForest.html): A forest of trees balanced by the AA tree
//! algorithm. Concatenation and separation do not require a reorganisation of the tree according to
//! search keys - only rebalancing will take place, the order of the sequence being the responsibility
//! of the user. The implementation is based on arena allocation, and tree queries and updates are
//! conducted iteratively, as in the corresponding AA tree structures above.
//!
//!  - [`WeightedAaForest`](./tree/bst/waaforest/struct.WeightedAaForest.html): This is similar to `AaForest`.
//! However, in addition to the actual payload, a node weight can be stored and tree subweights
//! are maintained.

#![warn(missing_docs)]
extern crate rand;
extern crate slab;

pub mod tree;
pub mod graph;
pub mod types;
pub mod prelude;
