use slab;
use std::cmp::Ordering;
use std::iter::empty;
use std::ops::{Index, IndexMut};
use tree::{Tgf, WeightedTree};
use tree::bst::{BinarySearchTree, BstDirection, OrderedTree};
use tree::traversal::{BinaryInOrder, BinaryInOrderIndices, Traversable};
use types::{DefaultWeightType, Keys, KeyType, NodeIndex, Values, ValueType, WeightType};

#[cfg(test)]
mod tests;

#[derive(Clone, Debug)]
struct Node<K, V, W>
where
    K: KeyType,
    V: ValueType,
    W: WeightType,
{
    key: K,
    value: V,
    level: usize,
    weight: W,
    subweight: W,
    parent: usize,
    children: [usize; 2],
}

impl<K, V, W> Node<K, V, W>
where
    K: KeyType,
    V: ValueType,
    W: WeightType,
{
    fn new() -> Self {
        Node {
            key: K::default(),
            value: V::default(),
            level: 0,
            weight: W::default(),
            subweight: W::default(),
            parent: 0,
            children: [0, 0],
        }
    }

    fn new_leaf(key: K, value: V, weight: W) -> Self {
        Node {
            key: key,
            value: value,
            level: 1,
            weight: weight,
            subweight: weight,
            parent: 0,
            children: [0, 0],
        }
    }
}

impl<K, V, W> Index<BstDirection> for Node<K, V, W>
where
    K: KeyType,
    V: ValueType,
    W: WeightType,
{
    type Output = usize;
    fn index(&self, index: BstDirection) -> &usize {
        &self.children[index as usize]
    }
}

impl<K, V, W> IndexMut<BstDirection> for Node<K, V, W>
where
    K: KeyType,
    V: ValueType,
    W: WeightType,
{
    fn index_mut(&mut self, index: BstDirection) -> &mut usize {
        &mut self.children[index as usize]
    }
}

impl<K, V, W> Index<usize> for Node<K, V, W>
where
    K: KeyType,
    V: ValueType,
    W: WeightType,
{
    type Output = usize;
    fn index(&self, index: usize) -> &usize {
        &self.children[index as usize]
    }
}

impl<K, V, W> IndexMut<usize> for Node<K, V, W>
where
    K: KeyType,
    V: ValueType,
    W: WeightType,
{
    fn index_mut(&mut self, index: usize) -> &mut usize {
        &mut self.children[index as usize]
    }
}

#[derive(Clone, Debug)]
pub struct WeightedAaTree<K, V, W = DefaultWeightType>
where
    K: KeyType,
    V: ValueType,
    W: WeightType,
{
    arena: slab::Slab<Node<K, V, W>>,
    root: usize,
    nil: usize,
}

impl<K, V, W> WeightedAaTree<K, V, W>
where
    K: KeyType,
    V: ValueType,
    W: WeightType,
{
    pub fn new(size: usize) -> Self {
        let mut a = slab::Slab::with_capacity(size + 1);
        let n = a.insert(Node::new());

        WeightedAaTree {
            arena: a,
            root: n,
            nil: n,
        }
    }

    fn compare(&self, key: &K, node: usize) -> Option<Ordering> {
        if node == self.nil {
            return None;
        }
        Some(key.cmp(&self.arena[node].key))
    }

    fn skew_node(&mut self, node: usize) -> usize {
        if node == self.nil {
            return node;
        }

        let node_level = self.arena[node].level;
        let left = self.arena[node][BstDirection::Left];
        let left_level = self.arena[left].level;
        let mut ret = node;

        if node_level == left_level {
            let parent = self.arena[node].parent;
            let dir = if self.arena[parent][BstDirection::Left] == node {
                BstDirection::Left
            } else {
                BstDirection::Right
            };
            let left_right = self.arena[left][BstDirection::Right];

            ret = left;
            self.link(parent, left, dir);
            self.link(left, node, BstDirection::Right);
            self.link(node, left_right, BstDirection::Left);
            self.update_weights(node);
            self.update_weights(left);
        }
        ret
    }

    fn split_node(&mut self, node: usize) -> usize {
        if node == self.nil {
            return node;
        }

        let node_level = self.arena[node].level;
        let right = self.arena[node][BstDirection::Right];
        let right_right = self.arena[right][BstDirection::Right];
        let right_right_level = self.arena[right_right].level;
        let mut ret = node;

        if right_right_level == node_level && node_level != 0 {
            let parent = self.arena[node].parent;
            let dir = if self.arena[parent][BstDirection::Left] == node {
                BstDirection::Left
            } else {
                BstDirection::Right
            };
            let right_left = self.arena[right][BstDirection::Left];

            ret = right;
            self.link(parent, right, dir);
            self.link(right, node, BstDirection::Left);
            self.link(node, right_left, BstDirection::Right);
            self.arena[right].level += 1;
            self.update_weights(node);
            self.update_weights(right);
        }
        ret
    }

    fn update_weights(&mut self, node: usize) {
        let left = self.arena[node][BstDirection::Left];
        let right = self.arena[node][BstDirection::Right];
        let subweight =
            self.arena[node].weight + self.arena[left].subweight + self.arena[right].subweight;
        self.arena[node].subweight = subweight;
    }

    fn link(&mut self, parent: usize, child: usize, dir: BstDirection) {
        if parent == child {
            return;
        }
        if parent != self.nil {
            self.arena[parent][dir] = child;
            if child != self.nil {
                self.arena[child].parent = parent;
            }
        } else {
            self.arena[child].parent = self.nil;
            self.root = child;
        }
    }

    fn unlink(&mut self, parent: usize, child: usize, dir: BstDirection) {
        if parent == child {
            return;
        }
        if parent != self.nil {
            self.arena[parent][dir] = self.nil;
            if child != self.nil {
                self.arena[child].parent = self.nil;
            }
        }
    }

    fn find_node(&self, key: &K) -> Option<usize> {
        let mut parent = self.root;
        let mut child;

        if parent == self.nil {
            return None;
        }

        loop {
            match self.compare(key, parent).unwrap_or(Ordering::Equal) {
                Ordering::Less => {
                    child = self.arena[parent][BstDirection::Left];
                }
                Ordering::Greater => {
                    child = self.arena[parent][BstDirection::Right];
                }
                Ordering::Equal => {
                    return Some(parent);
                }
            }

            if child == self.nil {
                return None;
            }
            parent = child;
        }
    }

    pub fn insert_weighted(&mut self, key: K, value: V, weight: W) {
        if self.root == self.nil {
            self.root = self.arena.insert(Node::new_leaf(key, value, weight));
            return;
        }

        let mut parent = self.root;
        let mut child;
        let mut dir;

        loop {
            match self.compare(&key, parent).unwrap_or(Ordering::Equal) {
                Ordering::Less => {
                    dir = BstDirection::Left;
                    child = self.arena[parent][BstDirection::Left];
                }
                Ordering::Greater => {
                    dir = BstDirection::Right;
                    child = self.arena[parent][BstDirection::Right];
                }
                Ordering::Equal => {
                    return;
                }
            }

            if child == self.nil {
                child = self.arena.insert(Node::new_leaf(key, value, weight));
                self.link(parent, child, dir);

                break;
            }

            parent = child;
        }

        loop {
            self.update_weights(child);
            child = self.skew_node(child);
            child = self.split_node(child);
            child = self.arena[child].parent;
            if child == self.nil {
                break;
            }
        }
    }
    fn next_from_subtree(&self, node: usize, dir: BstDirection) -> usize {
        let mut parent = self.arena[node][dir];
        let mut child;
        let other_dir = dir.other();
        loop {
            child = self.arena[parent][other_dir];
            if child == self.nil {
                break;
            }
            parent = child;
        }
        parent
    }

    fn next(&self, node: usize, dir: BstDirection) -> usize {
        let mut child = self.next_from_subtree(node, dir);
        if child != self.nil {
            return child;
        }

        child = self.arena[node].parent;
        if child == self.nil {
            return self.nil;
        }
        let other_dir = dir.other();
        let mut parent_dir = if self.arena[child][BstDirection::Left] == node {
            BstDirection::Left
        } else {
            BstDirection::Right
        };
        if parent_dir == other_dir {
            return child;
        }

        let mut parent = self.arena[child].parent;
        loop {
            if parent == self.nil {
                return self.nil;
            }
            parent_dir = if self.arena[parent][BstDirection::Left] == child {
                BstDirection::Left
            } else {
                BstDirection::Right
            };
            if parent_dir == other_dir {
                return child;
            }
            child = parent;
            parent = self.arena[child].parent;
        }
    }

    fn extreme(&self, node: usize, dir: BstDirection) -> usize {
        let mut parent = node;
        let mut child = self.arena[parent][dir];
        loop {
            if child == self.nil {
                break;
            }
            parent = child;
            child = self.arena[parent][dir];
        }
        parent
    }

    fn apply(
        &self,
        f: fn(&WeightedAaTree<K, V, W>, usize, BstDirection) -> usize,
        node: usize,
        dir: BstDirection,
    ) -> Option<usize> {
        if self.arena.get(node).is_some() {
            let ret = f(self, node, dir);
            if ret == self.nil {
                return None;
            }
            return Some(ret);
        }
        None
    }
}

impl<K, V, W> BinarySearchTree<K, V> for WeightedAaTree<K, V, W>
where
    K: KeyType,
    V: ValueType,
    W: WeightType,
{
    fn insert(&mut self, key: K, value: V) {
        self.insert_weighted(key, value, W::default());
    }

    fn remove(&mut self, key: &K) -> Option<V> {
        let node;
        match self.find_node(key) {
            Some(n) => {
                node = n;
            }
            None => {
                return None;
            }
        }

        let deleted = node;
        let deleted_left = self.arena[deleted][BstDirection::Left];
        let deleted_right = self.arena[deleted][BstDirection::Right];
        let mut parent = self.arena[node].parent;
        let dir = if self.arena[parent][BstDirection::Left] == node {
            BstDirection::Left
        } else {
            BstDirection::Right
        };

        self.unlink(parent, deleted, dir);
        self.unlink(deleted, deleted_left, BstDirection::Left);
        self.unlink(deleted, deleted_right, BstDirection::Right);

        let mut child;

        if deleted_left == self.nil {
            if deleted_right == self.nil {
                child = parent;
            } else {
                child = deleted_right;
                self.link(parent, child, dir);
                self.arena[child].level = self.arena[deleted].level;
            }
        } else if deleted_right == self.nil {
            child = deleted_left;
            self.link(parent, child, dir);
            self.arena[child].level = self.arena[deleted].level;
        } else {
            let mut heir_parent = self.nil;
            let mut heir = deleted_left;
            let mut heir_dir = BstDirection::Left;
            loop {
                let right = self.arena[heir][BstDirection::Right];
                if right == self.nil {
                    break;
                }
                heir_dir = BstDirection::Right;
                heir_parent = heir;
                heir = right;
            }

            child = heir;
            if heir_parent != self.nil {
                let left = self.arena[heir][BstDirection::Left];
                self.unlink(heir_parent, heir, heir_dir);
                self.unlink(heir, left, BstDirection::Left);
                self.link(heir_parent, left, BstDirection::Right);
                child = heir_parent;
            }
            self.link(parent, heir, dir);
            self.link(heir, deleted_left, BstDirection::Left);
            self.link(heir, deleted_right, BstDirection::Right);
            self.arena[heir].level = self.arena[deleted].level;
        }

        parent = self.arena[child].parent;

        loop {
            self.update_weights(child);
            let child_level = self.arena[child].level;
            let left_level = self.arena[self.arena[child][BstDirection::Left]].level;
            let right_level = self.arena[self.arena[child][BstDirection::Right]].level;

            if left_level + 1 < child_level || right_level + 1 < child_level {
                let new_child_level = child_level - 1;
                self.arena[child].level = new_child_level;
                let mut right = self.arena[child][BstDirection::Right];
                if right_level > new_child_level {
                    self.arena[right].level = new_child_level;
                }

                child = self.skew_node(child);
                right = self.arena[child][BstDirection::Right];
                right = self.skew_node(right);
                right = self.arena[right][BstDirection::Right];
                self.skew_node(right);
                child = self.split_node(child);
                right = self.arena[child][BstDirection::Right];
                self.split_node(right);
            }

            if parent == self.nil {
                self.root = child;
                return Some(self.arena.remove(deleted).value);
            }

            child = parent;
            parent = self.arena[child].parent;
        }
    }

    fn get(&self, key: &K) -> Option<usize> {
        self.find_node(key)
    }

    fn contains_key(&self, key: &K) -> bool {
        self.find_node(key).is_some()
    }

    fn key(&self, node: NodeIndex) -> Option<&K> {
        let node = node.index();
        if node == self.nil {
            return None;
        }
        self.arena.get(node).map(|n| &n.key)
    }
}

impl<K, V, W> Traversable<V> for WeightedAaTree<K, V, W>
where
    K: KeyType,
    V: ValueType,
    W: WeightType,
{
    fn root(&self, _node: NodeIndex) -> Option<NodeIndex> {
        if self.root == self.nil {
            return None;
        }
        Some(NodeIndex(self.root))
    }

    fn value(&self, node: NodeIndex) -> Option<&V> {
        let node = node.index();
        if node == self.nil {
            return None;
        }
        self.arena.get(node).map(|n| &n.value)
    }

    fn value_mut(&mut self, node: NodeIndex) -> Option<&mut V> {
        let node = node.index();
        if node == self.nil {
            return None;
        }
        self.arena.get_mut(node).map(|n| &mut n.value)
    }

    fn parent(&self, node: NodeIndex) -> Option<NodeIndex> {
        let node = node.index();
        match self.arena.get(node) {
            Some(n) => {
                let parent = n.parent;
                if parent == self.nil {
                    return None;
                }
                Some(NodeIndex(parent))
            }
            None => None,
        }
    }

    fn child(&self, node: NodeIndex, pos: usize) -> Option<NodeIndex> {
        let node = node.index();
        if let Some(n) = self.arena.get(node) {
            if pos > 1 {
                return None;
            }
            let child = n.children[pos];
            if child == self.nil {
                return None;
            }
            return Some(NodeIndex(child));
        }
        None
    }

    fn child_count(&self, node: NodeIndex) -> usize {
        let node = node.index();
        if let Some(_n) = self.arena.get(node) {
            if node != self.nil {
                return 2;
            }
        }
        0
    }

    fn node_count(&self) -> usize {
        self.arena.len() - 1
    }
}

impl<K, V, W> OrderedTree for WeightedAaTree<K, V, W>
where
    K: KeyType,
    V: ValueType,
    W: WeightType,
{
    fn sub_predecessor(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(
            WeightedAaTree::next_from_subtree,
            node.index(),
            BstDirection::Left,
        ).map(NodeIndex)
    }

    fn sub_successor(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(
            WeightedAaTree::next_from_subtree,
            node.index(),
            BstDirection::Right,
        ).map(NodeIndex)
    }

    fn predecessor(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(WeightedAaTree::next, node.index(), BstDirection::Left)
            .map(NodeIndex)
    }

    fn successor(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(WeightedAaTree::next, node.index(), BstDirection::Right)
            .map(NodeIndex)
    }

    fn first(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(WeightedAaTree::extreme, node.index(), BstDirection::Left)
            .map(NodeIndex)
    }

    fn last(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(WeightedAaTree::extreme, node.index(), BstDirection::Right)
            .map(NodeIndex)
    }

    fn is_smaller(&self, node_u: NodeIndex, node_v: NodeIndex) -> bool {
        let node_u = node_u.index();
        let node_v = node_v.index();
        if node_u == self.nil || node_v == self.nil {
            return false;
        }
        self.arena[node_u].key < self.arena[node_v].key
    }
}

impl<K, V, W> WeightedTree<W> for WeightedAaTree<K, V, W>
where
    K: KeyType,
    V: ValueType,
    W: WeightType,
{
    fn set_weight(&mut self, node: NodeIndex, weight: W) {
        let node = node.index();
        self.arena[node].weight = weight;
        let mut parent = node;

        loop {
            if parent == self.nil {
                break;
            }
            self.update_weights(parent);
            parent = self.arena[parent].parent;
        }
    }

    fn weight(&self, node: NodeIndex) -> W {
        self.arena
            .get(node.index())
            .map_or(W::default(), |n| n.weight)
    }

    fn subweight(&self, node: NodeIndex) -> W {
        self.arena
            .get(node.index())
            .map_or(W::default(), |n| n.subweight)
    }
}

impl<'slf, K, V, W> Keys<'slf, K> for WeightedAaTree<K, V, W>
where
    K: 'slf + KeyType,
    V: ValueType,
    W: WeightType,
{
    fn keys(&'slf self) -> Box<Iterator<Item=(NodeIndex, &'slf K)> + 'slf> {
        if self.root == self.nil {
            return Box::new(empty::<(NodeIndex, &'slf K)>());
        }
        Box::new(
            BinaryInOrderIndices::new(self, NodeIndex(self.root))
                .map(move |i| (i, &self.arena[i.index()].key)),
        )
    }
}

impl<'slf, K, V, W> Values<'slf, V> for WeightedAaTree<K, V, W>
where
    K: KeyType,
    V: 'slf + ValueType,
    W: WeightType,
{
    fn values(&'slf self) -> Box<Iterator<Item=(NodeIndex, &'slf V)> + 'slf> {
        if self.root == self.nil {
            return Box::new(empty::<(NodeIndex, &'slf V)>());
        }
        Box::new(BinaryInOrder::new(self, NodeIndex(self.root)))
    }
}

impl<K, V, W> Index<NodeIndex> for WeightedAaTree<K, V, W>
where
    K: KeyType,
    V: ValueType,
    W: WeightType,
{
    type Output = V;
    fn index(&self, index: NodeIndex) -> &V {
        &self.arena[index.index()].value
    }
}

impl<K, V, W> IndexMut<NodeIndex> for WeightedAaTree<K, V, W>
where
    K: KeyType,
    V: ValueType,
    W: WeightType,
{
    fn index_mut(&mut self, index: NodeIndex) -> &mut V {
        &mut self.arena[index.index()].value
    }
}

impl<K, V, W> Tgf for WeightedAaTree<K, V, W>
where
    K: KeyType,
    V: ValueType,
    W: WeightType,
{
    fn to_tgf(&self) -> String {
        let mut nodes = String::from("");
        let mut edges = String::from("");
        let iter = self.arena.iter();
        for (index, node) in iter {
            nodes.push_str(format!("{}", index).as_str());
            nodes.push_str(" [K = ");
            nodes.push_str(format!("{:?}", node.key).as_str());
            nodes.push_str(", L = ");
            nodes.push_str(format!("{}", node.level).as_str());
            nodes.push_str(" W = ");
            nodes.push_str(format!("{:?}", node.weight).as_str());
            nodes.push_str(", S = ");
            nodes.push_str(format!("{:?}", node.subweight).as_str());
            nodes.push_str("]\n");

            if node[BstDirection::Left] != self.nil {
                edges.push_str(format!("{}", index).as_str());
                edges.push_str(" ");
                edges.push_str(format!("{}", node[BstDirection::Left]).as_str());
                edges.push_str(" BstDirection::Left\n");
            }

            if node[BstDirection::Right] != self.nil {
                edges.push_str(format!("{}", index).as_str());
                edges.push_str(" ");
                edges.push_str(format!("{}", node[BstDirection::Right]).as_str());
                edges.push_str(" BstDirection::Right\n");
            }
        }
        nodes.push_str("#\n");
        nodes.push_str(edges.as_str());
        nodes
    }
}
