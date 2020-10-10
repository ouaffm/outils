# outils

**outils** is a graph and tree data structure library. It provides utilities which at the
time of writing were not available through other crates.

Please read the [API Documentation here](https://docs.rs/outils/).

[![](https://travis-ci.org/ouaffm/outils.svg?branch=master)](https://travis-ci.org/ouaffm/outils)
[![](http://meritbadge.herokuapp.com/outils)](https://crates.io/crates/outils)

## Utilities

### Fully dynamic connectivity for general graphs: 
A dynamic graph data structure is able to
answer queries as to whether two vertices are connected in a graph through a path of edges.
In this context, _fully dynamic_ means that the graph can be updated by insertions or
deletions of edges between queries (see also [Dynamic Connectivity][1]).

- [`DynamicGraph`][2]: Deterministic dynamic connectivity with query cost **O(log(n))** and update
costs of **O(log^2 (n))**. The structure also supports vertex weights, dynamically maintaining the
total weight of connected components.

### Balanced binary search trees:
A [balanced binary search tree][3] organizes search keys and
their associated payload in a way such that the resulting binary tree has a minimal height,
given the number of items stored, resulting in query and update costs of O(log(n)). This library
uses [AA trees][4], an abstraction of red-black trees, for balancing the trees after updates.

 - [`AaTree`][5]: An iterative AA tree implementation using [arena allocation][6]. For most use
cases, it is recommended to simply use the [`BTreeMap`][7] provided by the standard library, as
it is considerably faster (appr. 50%). However, if information on parent and child relations
between tree nodes, or custom traversal of the tree as such, are needed, `AaTree` has an advantage
over `BTreeMap`.

 - [`WeightedAaTree`][8]: This is similar to `AaTree`. However, in addition to the actual
payload, node weights can be stored and tree subweights are maintained.

### Balanced binary forests: 
A balanced binary forest is a forest of [balanced binary trees][3].
In contrast to the tree data structures above, the order of the payload is not determined by
associated search keys but by the relations of the nodes to each other: the in-order traversal
of a forest tree alone represents the order of its nodes. Forest trees can be concatenated or
split in order to manage those sequences. Parent and child relations are available, facilitating
analysis of the represented sequences.

 - [`AaForest`][9]: A forest of trees balanced by the [AA tree][4] algorithm. Concatenation and
separation do not require a reorganisation of the tree according to search keys - only
rebalancing will take place, the order of the sequence being the responsibility of the user.
The implementation is based on [arena allocation][6], and tree queries and updates are conducted
iteratively, as in the corresponding AA tree structures above.

 - [`WeightedAaForest`][10]: This is similar to `AaForest`. However, in addition to the actual
payload, a node weight can be stored and tree subweights are maintained.

### General purpose tree data structures:
- [`Forest`][11]: A generic forest of trees. The implementation is based on
[arena allocation][6] and a [first child/next sibling][12] representation, thus storing the
children of a node as a linked list headed by the first child of the parent node.

## Recent changes
- 0.3.0
  - **BREAKING:** Changed signatures of `AaTree` and `WeightedAaTree` to pass the search key by value
  as `KeyType` required keys to be `Copy`.
  - Added function input_pos() to `AaTree` and `WeightedAaTree` to expose the position in a tree 
  where a new key would be inserted.
- 0.2.0
  - Upgrade to Rust Edition 2018
- 0.1.3
  - Removed required implementation for Hash for types except `KeyType`
- 0.1.2
  - Added general purpose forest data structure
  - Fixed minor typos in documentation
- 0.1.1
  - Travis-CI support
  - Fixed minor typos in documentation
- 0.1.0
  - Initial version 

## Coming soon
- `FixedMemoryForest`: An extension of `Forest` that will not exceed its assigned capacity. Rather,
   the data structur will use _leaf recycling_ when the tree is filled to capacity. The basic idea is 
   to keep track of accesses to leaf nodes and discard those leaves that haven't been accessed for 
   the longest time, should it become necessary to free memory. 

[1]: https://en.wikipedia.org/wiki/Dynamic_connectivity
[2]: https://docs.rs/outils/0.1.2/outils/graph/dynconn/hdt/struct.DynamicGraph.html
[3]: https://en.wikipedia.org/wiki/Self-balancing_binary_search_tree
[4]: https://en.wikipedia.org/wiki/AA_tree
[5]: https://docs.rs/outils/0.1.2/outils/tree/bst/aatree/struct.AaTree.html
[6]: https://en.wikipedia.org/wiki/Region-based_memory_management
[7]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html
[8]: https://docs.rs/outils/0.1.2/outils/tree/bst/waatree/struct.WeightedAaTree.html
[9]: https://docs.rs/outils/0.1.2/outils/tree/bst/aaforest/struct.AaForest.html
[10]: https://docs.rs/outils/0.1.2/outils/tree/bst/waaforest/struct.WeightedAaForest.html
[11]: https://docs.rs/outils/0.1.2/outils/tree/generic/struct.Forest.html
[12]: https://en.wikipedia.org/wiki/Left-child_right-sibling_binary_tree