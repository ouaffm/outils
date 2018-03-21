use types::{DefaultIndexType, IndexType, KeyType, NodeIndex, ValueType};

pub mod aatree;
pub mod waatree;
pub mod aaforest;
pub mod waaforest;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum BstDirection {
    Left = 0,
    Right = 1,
}

impl BstDirection {
    #[inline]
    fn other(&self) -> BstDirection {
        match *self {
            BstDirection::Left => BstDirection::Right,
            BstDirection::Right => BstDirection::Left,
        }
    }
}

pub trait BinarySearchTree<K, V, Ix = DefaultIndexType>
where
    K: KeyType,
    V: ValueType,
    Ix: IndexType,
{
    fn insert(&mut self, key: K, value: V);
    fn remove(&mut self, key: &K) -> Option<V>;
    fn contains_key(&self, key: &K) -> bool;
    fn get(&self, key: &K) -> Option<Ix>;
    fn key(&self, node: NodeIndex<Ix>) -> Option<&K>;
}

pub trait OrderedTree<Ix = DefaultIndexType>
where
    Ix: IndexType,
{
    fn sub_predecessor(&self, node: NodeIndex<Ix>) -> Option<NodeIndex<Ix>>;
    fn sub_successor(&self, node: NodeIndex<Ix>) -> Option<NodeIndex<Ix>>;
    fn predecessor(&self, node: NodeIndex<Ix>) -> Option<NodeIndex<Ix>>;
    fn successor(&self, node: NodeIndex<Ix>) -> Option<NodeIndex<Ix>>;
    fn first(&self, node: NodeIndex<Ix>) -> Option<NodeIndex<Ix>>;
    fn last(&self, node: NodeIndex<Ix>) -> Option<NodeIndex<Ix>>;
    fn is_smaller(&self, node_u: NodeIndex<Ix>, node_v: NodeIndex<Ix>) -> bool;
}

pub trait BalancedBinaryForest<V, Ix = DefaultIndexType>
where
    V: ValueType,
    Ix: IndexType,
{
    fn insert(&mut self, value: V) -> NodeIndex<Ix>;
    fn remove(&mut self, node: NodeIndex<Ix>) -> Option<V>;
    fn split(
        &mut self,
        node: NodeIndex<Ix>,
        dir: BstDirection,
    ) -> (Option<NodeIndex<Ix>>, Option<NodeIndex<Ix>>);
    fn split_all(&mut self, node: NodeIndex<Ix>, size_hint: Option<usize>) -> Vec<NodeIndex<Ix>>;
    fn append(&mut self, node_u: NodeIndex<Ix>, node_v: NodeIndex<Ix>) -> Option<NodeIndex<Ix>>;
}
