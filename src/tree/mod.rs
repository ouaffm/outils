use slab;
use tree::traversal::Traversable;
use types::{DefaultIndexType, IndexType, NodeIndex, ValueType, WeightType};

pub mod bst;
pub mod traversal;

pub trait WeightedTree<W, Ix = DefaultIndexType>
where
    W: WeightType,
    Ix: IndexType,
{
    fn set_weight(&mut self, node: NodeIndex<Ix>, weight: W);
    fn weight(&self, node: NodeIndex<Ix>) -> W;
    fn subweight(&self, node: NodeIndex<Ix>) -> W;
}

pub trait Tgf {
    fn to_tgf(&self) -> String;
}

#[derive(Clone, Debug)]
struct Node<V>
where
    V: ValueType,
{
    value: V,
    parent: Option<usize>,
    children: Vec<usize>,
}

impl<V> Node<V>
where
    V: ValueType,
{
    fn new() -> Self {
        Node {
            value: V::default(),
            parent: None,
            children: Vec::new(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct GenericTree<V>
where
    V: ValueType,
{
    arena: slab::Slab<Node<V>>,
    root: Option<usize>,
}

impl<V> GenericTree<V>
where
    V: ValueType,
{
    pub fn new(size: usize) -> Self {
        GenericTree {
            arena: slab::Slab::with_capacity(size),
            root: None,
        }
    }

    pub fn set_root_value(&mut self, value: V) -> usize {
        if let Some(rt) = self.root {
            self.arena[rt].value = value;
            return rt;
        } else {
            let mut n = Node::new();
            n.value = value;
            let rt = self.arena.insert(n);
            self.root = Some(rt);
            return rt;
        }
    }

    pub fn set_node_value(&mut self, node: usize, value: V) {
        if let Some(node) = self.arena.get_mut(node) {
            node.value = value;
        }
    }

    pub fn add_child(&mut self, parent: usize, value: V) -> Option<usize> {
        self.arena.get(parent)?;
        let mut child_node = Node::new();
        child_node.parent = Some(parent);
        child_node.value = value;
        let child = self.arena.insert(child_node);
        let parent_node = self.arena.get_mut(parent).unwrap();
        parent_node.children.push(child);
        Some(parent_node.children.len() - 1)
    }
}

impl<V> Traversable<V> for GenericTree<V>
where
    V: ValueType,
{
    fn root(&self, _node: NodeIndex) -> Option<NodeIndex> {
        self.root.map(NodeIndex)
    }

    fn value(&self, node: NodeIndex) -> Option<&V> {
        self.arena.get(node.index()).map(|n| &n.value)
    }

    fn value_mut(&mut self, node: NodeIndex) -> Option<&mut V> {
        self.arena.get_mut(node.index()).map(|n| &mut n.value)
    }

    fn parent(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.arena
            .get(node.index())
            .and_then(|n| n.parent)
            .map(NodeIndex)
    }

    fn child(&self, node: NodeIndex, pos: usize) -> Option<NodeIndex> {
        self.arena
            .get(node.index())
            .and_then(|n| n.children.get(pos))
            .map(|r| NodeIndex(*r))
    }

    fn child_count(&self, node: NodeIndex) -> usize {
        self.arena.get(node.index()).map_or(0, |n| n.children.len())
    }

    fn node_count(&self) -> usize {
        self.arena.len()
    }
}
