//! Tree data structures and algorithms
use types::{DefaultIndexType, IndexType, NodeIndex, WeightType};

pub mod bst;
pub mod traversal;

/// Trees implementing this trait are able to maintain node weights and subweights. The subweight
/// of a tree node is recursively defined as the sum of its own weight plus the subweights of its
/// children. The subweight of a leaf node is equal to its weight.
pub trait WeightedTree<W, Ix = DefaultIndexType>
where
    W: WeightType,
    Ix: IndexType,
{
    /// Set the weight of the tree node indexed by `node` to `weight` and update the subweight
    /// of this node as well as the subweights of the nodes on the path from this node to the tree
    /// root.
    fn set_weight(&mut self, node: NodeIndex<Ix>, weight: W);

    /// Immutably access the weight of the tree node indexed by `node`.
    fn weight(&self, node: NodeIndex<Ix>) -> Option<&W>;

    /// Immutably access the subweight of the tree node indexed by `node`.
    fn subweight(&self, node: NodeIndex<Ix>) -> Option<&W>;

    /// Change the weight of tree node indexed by `node` by applying the closure `f`. After applying
    /// the closure, the subweight of this node as well as the subweights of the nodes on the path
    /// from this node to the tree root will be updated accordingly.
    fn adjust_weight(&mut self, node: NodeIndex<Ix>, f: &Fn(&mut W));
}
