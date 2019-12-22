//! Binary tree data structures and algorithms
use crate::types::{DefaultIndexType, IndexType, KeyType, NodeIndex, ValueType};

pub mod aaforest;
pub mod aatree;
pub mod waaforest;
pub mod waatree;

/// Enum to refer to the two possible traversal directions of a binary tree
/// (i.e. `Left` and `Right`) in a type-safe way.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum BstDirection {
    /// The left child of binary tree node.
    Left = 0,
    /// The right child of a binary tree node.
    Right = 1,
}

impl BstDirection {
    /// Returns the opposite direction
    #[inline]
    fn other(self) -> BstDirection {
        match self {
            BstDirection::Left => BstDirection::Right,
            BstDirection::Right => BstDirection::Left,
        }
    }
}

/// This trait defines the fundamental operations of a binary search tree.
pub trait BinarySearchTree<K, V, Ix = DefaultIndexType>
where
    K: KeyType,
    V: ValueType,
    Ix: IndexType,
{
    /// Inserts a key-value pair into the tree. If the tree did not have this `key` present, `None`
    /// is returned. If the tree **did** have this `key` present, the value is updated, and the old
    /// value is returned. Note that in this situation, the key is left unchanged.
    fn insert(&mut self, key: K, value: V) -> Option<V>;

    /// Removes a `key` from the tree if present, in this case returning the associated value.
    fn remove(&mut self, key: &K) -> Option<V>;

    /// Returns `true` if the map contains a value for the specified `key`.
    fn contains_key(&self, key: &K) -> bool;

    /// Returns an immutable reference to the associated value of the specified `key`.
    fn get(&self, key: &K) -> Option<&V>;

    /// Returns a mutable reference to the associated value of the specified `key`.
    fn get_mut(&mut self, key: &K) -> Option<&mut V>;

    /// Returns the index of the tree node holding the specified `key`.
    fn index(&self, key: &K) -> Option<NodeIndex<Ix>>;

    /// Returns the  key held by the tree node indexed by `node`.
    fn key(&self, node: NodeIndex<Ix>) -> Option<&K>;
}

/// This trait defines operations for navigating the binary tree with respect to its in-order.
pub trait OrderedTree<Ix = DefaultIndexType>
where
    Ix: IndexType,
{
    /// Returns the biggest node of the left subtree of the tree node indexed by `node`.
    fn sub_predecessor(&self, node: NodeIndex<Ix>) -> Option<NodeIndex<Ix>>;

    /// Returns the smallest node of the right subtree of the tree node indexed by `node`.
    fn sub_successor(&self, node: NodeIndex<Ix>) -> Option<NodeIndex<Ix>>;

    /// Returns the biggest node of the whole tree which is smaller than the tree node
    /// indexed by `node`.
    fn predecessor(&self, node: NodeIndex<Ix>) -> Option<NodeIndex<Ix>>;

    /// Returns the smallest node of the whole tree which is bigger than the tree node
    /// indexed by `node`.
    fn successor(&self, node: NodeIndex<Ix>) -> Option<NodeIndex<Ix>>;

    /// Returns the smallest node of the left subtree of the tree node indexed by `node`.
    fn first(&self, node: NodeIndex<Ix>) -> Option<NodeIndex<Ix>>;

    /// Returns the biggest node of the right subtree of the tree node indexed by `node`.
    fn last(&self, node: NodeIndex<Ix>) -> Option<NodeIndex<Ix>>;

    /// Returns `true` if the tree node indexed by `node_u` is smaller than the tree node
    /// indexed by `node_v`. Otherwise, and in particular if one of the specified indices
    /// is invalid, `false` is returned.
    fn is_smaller(&self, node_u: NodeIndex<Ix>, node_v: NodeIndex<Ix>) -> bool;
}

/// This trait defines the fundamental operations of a balanced binary forest.
///
/// The main difference between a `BinarySearchTree` and a `BalancedBinaryForest` is that the order
/// of the latter is not determined by means of search keys associated to the nodes of the tree.
/// Rather, the order is solely determined by the in-order of the nodes which is under
/// control of the user.
///
/// Not using dedicated search keys enables this data structure to provide efficient operations to
/// split and concatenate the sequences represented by the forest trees. The usage of search keys
/// would require a significant number of insert and delete operation in order to split or concatenate
/// trees, while without search keys only re-balancing is required.
pub trait BalancedBinaryForest<V, Ix = DefaultIndexType>
where
    V: ValueType,
    Ix: IndexType,
{
    /// Inserts `value` into the forest as a new singleton (i.e. sole leaf) node.
    fn insert(&mut self, value: V) -> NodeIndex<Ix>;

    /// Removes the tree node indexed by `node`, returning its content in case of a valid index.
    fn remove(&mut self, node: NodeIndex<Ix>) -> Option<V>;

    /// Splits the sequence of tree nodes represented by the forest tree containing the tree node
    /// indexed by `node`.
    ///
    /// If `dir == BstDirection::Left`, `node` will index the last tree node of the left sequence,
    /// while if `dir == BstDirection::Right`, `node` will index the first tree node of the right
    /// sequence (both with respect to in-order). The roots of the resulting sequences will be
    /// returned as a tuple.
    fn split(
        &mut self,
        node: NodeIndex<Ix>,
        dir: BstDirection,
    ) -> (Option<NodeIndex<Ix>>, Option<NodeIndex<Ix>>);

    /// Splits the whole sequence of tree nodes represented by the forest tree containing the tree
    /// node indexed by `node` into singleton (i.e. sole leaf) nodes.
    ///
    /// If the tree nodes to be split is known beforehand, it can be specified optionally as
    /// the `size_hint` of the returned `Vec` containing the split tree nodes.
    ///
    /// Generally, this operation will be much faster than calling `split` on each node of the
    /// sequence separately, the reason being that no re-balancing is necessary when it is known
    /// beforehand that every tree node will be split.
    fn split_all(&mut self, node: NodeIndex<Ix>, size_hint: Option<usize>) -> Vec<NodeIndex<Ix>>;

    /// Concatenate the sequences of tree nodes represented by the forest trees containing the
    /// tree nodes indexed by `node_u` and `node_v`, respectively.
    ///
    /// With respect to in-order, the former sequence will represent the _smaller_ part of the
    /// new sequence, the latter sequence the _bigger_ part. The root of the resulting sequence will
    /// be returned.
    fn append(&mut self, node_u: NodeIndex<Ix>, node_v: NodeIndex<Ix>) -> Option<NodeIndex<Ix>>;
}
