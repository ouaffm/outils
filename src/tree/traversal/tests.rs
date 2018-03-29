use slab;
use super::{BinaryInOrderIndices, BinaryPostOrderIndices, BinaryPreOrderIndices,
            GeneralBfsIndices, GeneralDfsIndices, Traversable};
use tree::bst::aaforest::AaForest;
use tree::bst::BalancedBinaryForest;
use types::{NodeIndex, Tgf, ValueType};

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
struct GenericTree<V>
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

#[test]
fn test_generic_dfs() {
    let tree = build_generic_tree();
    let mut v = Vec::new();
    rec_general_dfs(&tree, NodeIndex(0), &mut v);

    let t = GeneralDfsIndices::new(&tree, NodeIndex(0));
    let seq = t.fold(Vec::new(), |mut v, i| {
        v.push(i);
        v
    });

    println!("{:?}", v);
    println!("{:?}", seq);

    assert!(v.len() == seq.len());

    for i in 0..v.len() {
        assert!(v[i] == seq[i]);
    }
}

#[test]
fn test_generic_bfs() {
    let tree = build_generic_tree();

    let t = GeneralBfsIndices::new(&tree, NodeIndex(0));
    let seq = t.fold(Vec::new(), |mut v, i| {
        v.push(i);
        v
    });

    println!("{:?}", seq);

    for i in 0..seq.len() {
        if i != 0 {
            assert!(seq[i] > seq[i - 1]);
        }
    }
}

#[test]
fn test_generic_complete_binary_inorder() {
    let tree = build_complete_binary_generic_tree();
    let mut v = Vec::new();
    rec_binary_inorder(&tree, NodeIndex(0), &mut v);

    let t = BinaryInOrderIndices::new(&tree, NodeIndex(0));
    let seq = t.fold(Vec::new(), |mut v, i| {
        v.push(i);
        v
    });

    println!("{:?}", v);
    println!("{:?}", seq);
    assert!(v.len() == seq.len());

    for i in 0..v.len() {
        assert!(v[i] == seq[i]);
    }
}

#[test]
fn test_generic_incomplete_binary_inorder() {
    let tree = build_incomplete_binary_generic_tree();
    let mut v = Vec::new();
    rec_binary_inorder(&tree, NodeIndex(0), &mut v);

    let t = BinaryInOrderIndices::new(&tree, NodeIndex(0));
    let seq = t.fold(Vec::new(), |mut v, i| {
        v.push(i);
        v
    });

    println!("{:?}", v);
    println!("{:?}", seq);

    assert!(v.len() == seq.len());

    for i in 0..v.len() {
        assert!(v[i] == seq[i]);
    }
}

#[test]
fn test_generic_complete_binary_preorder() {
    let tree = build_complete_binary_generic_tree();
    let mut v = Vec::new();
    rec_binary_preorder(&tree, NodeIndex(0), &mut v);

    let t = BinaryPreOrderIndices::new(&tree, NodeIndex(0));
    let seq = t.fold(Vec::new(), |mut v, i| {
        v.push(i);
        v
    });

    println!("{:?}", v);
    println!("{:?}", seq);

    assert!(v.len() == seq.len());

    for i in 0..v.len() {
        assert!(v[i] == seq[i]);
    }
}

#[test]
fn test_generic_incomplete_binary_preorder() {
    let tree = build_incomplete_binary_generic_tree();
    let mut v = Vec::new();
    rec_binary_preorder(&tree, NodeIndex(0), &mut v);

    let t = BinaryPreOrderIndices::new(&tree, NodeIndex(0));
    let seq = t.fold(Vec::new(), |mut v, i| {
        v.push(i);
        v
    });

    println!("{:?}", v);
    println!("{:?}", seq);

    assert!(v.len() == seq.len());

    for i in 0..v.len() {
        assert!(v[i] == seq[i]);
    }
}

#[test]
fn test_generic_complete_binary_postorder() {
    let tree = build_complete_binary_generic_tree();
    let mut v = Vec::new();
    rec_binary_postorder(&tree, NodeIndex(0), &mut v);

    let t = BinaryPostOrderIndices::new(&tree, NodeIndex(0));
    let seq = t.fold(Vec::new(), |mut v, i| {
        v.push(i);
        v
    });

    println!("{:?}", v);
    println!("{:?}", seq);

    assert!(v.len() == seq.len());

    for i in 0..v.len() {
        assert!(v[i] == seq[i]);
    }
}

#[test]
fn test_generic_incomplete_binary_postorder() {
    let tree = build_incomplete_binary_generic_tree();
    let mut v = Vec::new();
    rec_binary_postorder(&tree, NodeIndex(0), &mut v);

    let t = BinaryPostOrderIndices::new(&tree, NodeIndex(0));
    let seq = t.fold(Vec::new(), |mut v, i| {
        v.push(i);
        v
    });

    println!("{:?}", v);
    println!("{:?}", seq);

    assert!(v.len() == seq.len());

    for i in 0..v.len() {
        assert!(v[i] == seq[i]);
    }
}

#[test]
fn test_binary_inorder() {
    let tree = build_binary_tree();
    let v = vec![
        NodeIndex(3),
        NodeIndex(4),
        NodeIndex(5),
        NodeIndex(6),
        NodeIndex(7),
        NodeIndex(8),
    ];

    println!("{}", tree.to_tgf());

    let t = BinaryInOrderIndices::new(&tree, NodeIndex(3));
    let seq = t.fold(Vec::new(), |mut v, i| {
        v.push(i);
        v
    });

    println!("{:?}", v);
    println!("{:?}", seq);

    assert!(v.len() == seq.len());

    for i in 0..v.len() {
        assert!(v[i] == seq[i]);
    }
}

#[test]
fn test_binary_preorder() {
    let tree = build_binary_tree();
    let v = vec![
        NodeIndex(4),
        NodeIndex(3),
        NodeIndex(6),
        NodeIndex(5),
        NodeIndex(7),
        NodeIndex(8),
    ];

    let t = BinaryPreOrderIndices::new(&tree, NodeIndex(3));
    let seq = t.fold(Vec::new(), |mut v, i| {
        v.push(i);
        v
    });

    println!("{:?}", v);
    println!("{:?}", seq);

    assert!(v.len() == seq.len());

    for i in 0..v.len() {
        assert!(v[i] == seq[i]);
    }
}

#[test]
fn test_binary_postorder() {
    let tree = build_binary_tree();
    let v = vec![
        NodeIndex(3),
        NodeIndex(5),
        NodeIndex(8),
        NodeIndex(7),
        NodeIndex(6),
        NodeIndex(4),
    ];

    let t = BinaryPostOrderIndices::new(&tree, NodeIndex(3));
    let seq = t.fold(Vec::new(), |mut v, i| {
        v.push(i);
        v
    });

    println!("{:?}", v);
    println!("{:?}", seq);

    assert!(v.len() == seq.len());

    for i in 0..v.len() {
        assert!(v[i] == seq[i]);
    }
}

fn rec_binary_inorder(tree: &GenericTree<&str>, node: NodeIndex, v: &mut Vec<NodeIndex>) {
    let left = tree.child(node, 0);
    let right = tree.child(node, 1);
    left.map(|l| rec_binary_inorder(tree, l, v));
    v.push(node);
    right.map(|r| rec_binary_inorder(tree, r, v));
}

fn rec_binary_preorder(tree: &GenericTree<&str>, node: NodeIndex, v: &mut Vec<NodeIndex>) {
    let left = tree.child(node, 0);
    let right = tree.child(node, 1);
    v.push(node);
    left.map(|l| rec_binary_preorder(tree, l, v));
    right.map(|r| rec_binary_preorder(tree, r, v));
}

fn rec_binary_postorder(tree: &GenericTree<&str>, node: NodeIndex, v: &mut Vec<NodeIndex>) {
    let left = tree.child(node, 0);
    let right = tree.child(node, 1);
    left.map(|l| rec_binary_postorder(tree, l, v));
    right.map(|r| rec_binary_postorder(tree, r, v));
    v.push(node);
}

fn rec_general_dfs(tree: &GenericTree<&str>, node: NodeIndex, v: &mut Vec<NodeIndex>) {
    v.push(node);
    let mut pos = 0;
    while let Some(c) = tree.child(node, pos) {
        rec_general_dfs(tree, c, v);
        pos = pos + 1;
    }
}

fn build_complete_binary_generic_tree() -> GenericTree<&'static str> {
    let mut tree = GenericTree::new(31);
    tree.set_root_value("0");
    tree.add_child(0, "1");
    tree.add_child(0, "2");
    tree.add_child(1, "3");
    tree.add_child(1, "4");
    tree.add_child(2, "5");
    tree.add_child(2, "6");
    tree.add_child(3, "7");
    tree.add_child(3, "8");
    tree.add_child(4, "9");
    tree.add_child(4, "10");
    tree.add_child(5, "11");
    tree.add_child(5, "12");
    tree.add_child(6, "13");
    tree.add_child(6, "14");
    tree.add_child(7, "15");
    tree.add_child(7, "16");
    tree.add_child(8, "17");
    tree.add_child(8, "18");
    tree.add_child(9, "19");
    tree.add_child(9, "20");
    tree.add_child(10, "21");
    tree.add_child(10, "22");
    tree.add_child(11, "23");
    tree.add_child(11, "24");
    tree.add_child(12, "25");
    tree.add_child(12, "26");
    tree.add_child(13, "27");
    tree.add_child(13, "28");
    tree.add_child(14, "29");
    tree.add_child(14, "30");
    tree
}

fn build_incomplete_binary_generic_tree() -> GenericTree<&'static str> {
    let mut tree = GenericTree::new(31);
    tree.set_root_value("0");
    tree.add_child(0, "1");
    tree.add_child(0, "2");
    tree.add_child(1, "3");
    tree.add_child(1, "4");
    tree.add_child(2, "5");
    tree.add_child(2, "6");
    tree.add_child(3, "7");
    tree.add_child(3, "8");
    tree.add_child(4, "9");
    tree.add_child(4, "10");
    tree.add_child(5, "11");
    tree.add_child(5, "12");
    tree.add_child(6, "13");
    tree.add_child(7, "15");
    tree.add_child(7, "16");
    tree.add_child(8, "18");
    tree.add_child(9, "19");
    tree.add_child(9, "20");
    tree.add_child(10, "21");
    tree.add_child(10, "22");
    tree.add_child(11, "23");
    tree.add_child(11, "24");
    tree.add_child(12, "26");
    tree.add_child(13, "27");
    tree.add_child(13, "28");
    tree
}

fn build_generic_tree() -> GenericTree<&'static str> {
    let mut tree = GenericTree::new(31);
    tree.set_root_value("0");
    tree.add_child(0, "1");
    tree.add_child(0, "2");
    tree.add_child(0, "3");
    tree.add_child(0, "4");
    tree.add_child(1, "5");
    tree.add_child(1, "6");
    tree.add_child(1, "7");
    tree.add_child(2, "8");
    tree.add_child(2, "9");
    tree.add_child(3, "10");
    tree.add_child(4, "11");
    tree.add_child(4, "12");
    tree.add_child(5, "13");
    tree.add_child(5, "14");
    tree.add_child(6, "15");
    tree.add_child(7, "16");
    tree.add_child(7, "17");
    tree.add_child(8, "18");
    tree.add_child(8, "19");
    tree.add_child(8, "20");
    tree.add_child(9, "21");
    tree.add_child(9, "22");
    tree.add_child(10, "23");
    tree.add_child(11, "24");
    tree.add_child(12, "25");
    tree.add_child(12, "26");
    tree.add_child(15, "27");
    tree.add_child(15, "28");
    tree.add_child(15, "29");
    tree.add_child(16, "30");
    tree
}

fn build_binary_tree() -> AaForest<&'static str> {
    let mut tree = AaForest::new(6);
    let n1 = tree.insert("1");
    let n2 = tree.insert("2");
    let n3 = tree.insert("3");
    let n4 = tree.insert("4");
    let n5 = tree.insert("5");
    let n6 = tree.insert("6");
    let mut rt = tree.append(n1, n2).unwrap();
    rt = tree.append(rt, n3).unwrap();
    rt = tree.append(rt, n4).unwrap();
    rt = tree.append(rt, n5).unwrap();
    tree.append(rt, n6);
    tree
}
