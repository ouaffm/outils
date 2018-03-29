use types::{DefaultIndexType, IndexType, NodeIndex, WeightType};

pub mod bst;
pub mod traversal;

pub trait WeightedTree<W, Ix = DefaultIndexType>
where
    W: WeightType,
    Ix: IndexType,
{
    fn set_weight(&mut self, node: NodeIndex<Ix>, weight: W);
    fn weight(&self, node: NodeIndex<Ix>) -> Option<&W>;
    fn subweight(&self, node: NodeIndex<Ix>) -> Option<&W>;
    fn adjust_weight(&mut self, node: NodeIndex<Ix>, f: &Fn(&mut W));
}
