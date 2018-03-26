use slab;
use std::ops::{Index, IndexMut};
use tree::{Tgf, WeightedTree};
use tree::bst::{BalancedBinaryForest, BstDirection, OrderedTree};
use tree::traversal::{BinaryPreOrderIndices, Traversable};
use types::{DefaultWeightType, NodeIndex, Values, ValueType, WeightType};

#[cfg(test)]
mod tests;

#[derive(Clone, Debug)]
struct Node<V, W>
where
    V: ValueType,
    W: WeightType,
{
    value: V,
    level: usize,
    weight: W,
    subweight: W,
    parent: usize,
    children: [usize; 2],
}

impl<V, W> Node<V, W>
where
    V: ValueType,
    W: WeightType,
{
    fn new() -> Self {
        Node {
            value: V::default(),
            weight: W::default(),
            subweight: W::default(),
            level: 0,
            parent: 0,
            children: [0, 0],
        }
    }

    fn new_leaf(value: V) -> Self {
        Node {
            value: value,
            weight: W::default(),
            subweight: W::default(),
            level: 1,
            parent: 0,
            children: [0, 0],
        }
    }
}

impl<V, W> Index<BstDirection> for Node<V, W>
where
    V: ValueType,
    W: WeightType,
{
    type Output = usize;
    fn index(&self, index: BstDirection) -> &usize {
        &self.children[index as usize]
    }
}

impl<V, W> IndexMut<BstDirection> for Node<V, W>
where
    V: ValueType,
    W: WeightType,
{
    fn index_mut(&mut self, index: BstDirection) -> &mut usize {
        &mut self.children[index as usize]
    }
}

impl<V, W> Index<usize> for Node<V, W>
where
    V: ValueType,
    W: WeightType,
{
    type Output = usize;
    fn index(&self, index: usize) -> &usize {
        &self.children[index as usize]
    }
}

impl<V, W> IndexMut<usize> for Node<V, W>
where
    V: ValueType,
    W: WeightType,
{
    fn index_mut(&mut self, index: usize) -> &mut usize {
        &mut self.children[index as usize]
    }
}

#[derive(Clone, Debug)]
pub struct WeightedAaForest<V, W = DefaultWeightType>
where
    V: ValueType,
    W: WeightType,
{
    arena: slab::Slab<Node<V, W>>,
    nil: usize,
    jdummy: usize,
    sdummy: usize,
}

impl<V, W> WeightedAaForest<V, W>
where
    V: ValueType,
    W: WeightType,
{
    pub fn new(size: usize) -> Self {
        let mut a = slab::Slab::with_capacity(size + 3);
        let n = a.insert(Node::new());
        let dj = a.insert(Node::new());
        let ds = a.insert(Node::new());
        WeightedAaForest {
            arena: a,
            nil: n,
            jdummy: dj,
            sdummy: ds,
        }
    }

    #[inline]
    fn is_valid_index(&self, node: usize) -> bool {
        node > self.sdummy && self.arena.contains(node)
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

    fn init_dummy(&mut self, dummy: usize) {
        let dummy = dummy;
        self.arena[dummy].parent = self.nil;
        self.arena[dummy][BstDirection::Left] = self.nil;
        self.arena[dummy][BstDirection::Right] = self.nil;
        self.arena[dummy].level = 1;
        self.arena[dummy].weight = W::default();
        self.arena[dummy].subweight = W::default();
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

    fn root_and_height(&self, node: usize) -> (usize, usize) {
        let mut root = node;
        let mut height = 0;
        loop {
            if self.arena[root].parent == self.nil {
                break;
            }
            height += 1;
            root = self.arena[root].parent;
        }
        (root, height)
    }

    fn directions_to_root(&self, node: usize, height: usize) -> u64 {
        let mut path: u64 = 0;
        let mut child = node;
        let mut parent = self.arena[child].parent;
        let mut dir = if self.arena[parent][BstDirection::Left] == child {
            BstDirection::Left
        } else {
            BstDirection::Right
        };
        let mut i = height;

        loop {
            if parent == self.nil {
                break;
            }
            path |= (dir as u64) << i;
            child = parent;
            parent = self.arena[child].parent;
            dir = if self.arena[parent][BstDirection::Left] == child {
                BstDirection::Left
            } else {
                BstDirection::Right
            };
            i -= 1;
        }
        path >> 1
    }

    fn apply(
        &self,
        f: fn(&WeightedAaForest<V, W>, usize, BstDirection) -> usize,
        node: usize,
        dir: BstDirection,
    ) -> Option<usize> {
        if self.arena.get(node).is_some() {
            let ret = f(self, node, dir);
            if ret <= self.sdummy {
                return None;
            }
            return Some(ret);
        }
        None
    }

    fn isolate(&mut self, node: usize) -> usize {
        if node == self.nil {
            return self.nil;
        }

        let isolated = node;
        let isolated_left = self.arena[isolated][BstDirection::Left];
        let isolated_right = self.arena[isolated][BstDirection::Right];
        let mut parent = self.arena[node].parent;
        let dir = if self.arena[parent][BstDirection::Left] == node {
            BstDirection::Left
        } else {
            BstDirection::Right
        };

        self.unlink(parent, isolated, dir);
        self.unlink(isolated, isolated_left, BstDirection::Left);
        self.unlink(isolated, isolated_right, BstDirection::Right);

        let mut child;

        if isolated_left == self.nil {
            if isolated_right == self.nil {
                child = parent;
            } else {
                child = isolated_right;
                self.link(parent, child, dir);
                self.arena[child].level = self.arena[isolated].level;
            }
        } else if isolated_right == self.nil {
            child = isolated_left;
            self.link(parent, child, dir);
            self.arena[child].level = self.arena[isolated].level;
        } else {
            let mut heir_parent = self.nil;
            let mut heir = isolated_left;
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
            self.link(heir, isolated_left, BstDirection::Left);
            self.link(heir, isolated_right, BstDirection::Right);
            self.arena[heir].level = self.arena[isolated].level;
        }

        parent = self.arena[child].parent;
        loop {
            self.update_weights(child);
            child = self.fix_node_balance(child);

            if parent == self.nil {
                return child;
            }

            child = parent;
            parent = self.arena[child].parent;
        }
    }

    fn fix_node_balance(&mut self, node: usize) -> usize {
        let mut parent = node;
        let parent_level = self.arena[parent].level;
        let left_level = self.arena[self.arena[parent][BstDirection::Left]].level;
        let right_level = self.arena[self.arena[parent][BstDirection::Right]].level;

        if left_level + 1 < parent_level || right_level + 1 < parent_level {
            let new_parent_level = parent_level - 1;
            self.arena[parent].level = new_parent_level;
            let mut right = self.arena[parent][BstDirection::Right];
            if right_level > new_parent_level {
                self.arena[right].level = new_parent_level;
            }

            parent = self.skew_node(parent);
            right = self.arena[parent][BstDirection::Right];
            right = self.skew_node(right);
            right = self.arena[right][BstDirection::Right];
            self.skew_node(right);
            parent = self.split_node(parent);
            right = self.arena[parent][BstDirection::Right];
            self.split_node(right);
        }
        parent
    }

    fn join_at(&mut self, at: usize, left: usize, right: usize) -> usize {
        self.arena[at].level = 1;
        self.arena[at].subweight = self.arena[at].weight;
        let mut parent = self.append(NodeIndex(left), NodeIndex(at))
            .map_or(self.nil, |p| p.index());
        parent = self.append(NodeIndex(parent), NodeIndex(right))
            .map_or(self.nil, |p| p.index());
        parent
    }

    fn rotate(&mut self, parent: usize, child: usize) {
        if self.arena[child].parent != parent {
            return;
        }

        let grandparent = self.arena[parent].parent;
        let parent_dir = if self.arena[grandparent][BstDirection::Left] == parent {
            BstDirection::Left
        } else {
            BstDirection::Right
        };
        let child_dir = if self.arena[parent][BstDirection::Left] == child {
            BstDirection::Left
        } else {
            BstDirection::Right
        };
        let other_dir = child_dir.other();
        let grandchild = self.arena[child][other_dir];

        self.unlink(grandparent, parent, parent_dir);
        self.unlink(parent, child, child_dir);
        self.unlink(child, grandchild, other_dir);
        self.update_weights(child);

        let other_child = if child_dir == BstDirection::Right {
            let left = self.arena[parent][BstDirection::Left];
            self.unlink(parent, left, BstDirection::Left);
            self.join_at(parent, left, grandchild)
        } else {
            let right = self.arena[parent][BstDirection::Right];
            self.unlink(parent, right, BstDirection::Right);
            self.join_at(parent, grandchild, right)
        };
        self.link(child, other_child, other_dir);
        self.update_weights(child);
        self.link(grandparent, child, parent_dir);
    }
}

impl<V, W> BalancedBinaryForest<V> for WeightedAaForest<V, W>
where
    V: ValueType,
    W: WeightType,
{
    fn insert(&mut self, value: V) -> NodeIndex {
        NodeIndex(self.arena.insert(Node::new_leaf(value)))
    }

    fn remove(&mut self, node: NodeIndex) -> Option<V> {
        let node = node.index();
        if node <= self.sdummy {
            return None;
        }

        self.arena.get(node)?;
        self.isolate(node);
        Some(self.arena.remove(node).value)
    }

    fn split(
        &mut self,
        node: NodeIndex,
        dir: BstDirection,
    ) -> (Option<NodeIndex>, Option<NodeIndex>) {
        let node = node.index();
        if node <= self.sdummy || !self.arena.contains(node) {
            return (None, None);
        }

        let dummy = self.sdummy;
        self.init_dummy(dummy);

        if dir == BstDirection::Left {
            let succ = self.next_from_subtree(node, BstDirection::Right);
            if succ == self.nil {
                self.link(node, dummy, BstDirection::Right);
            } else {
                self.link(succ, dummy, BstDirection::Left);
            }
        } else {
            let pred = self.next_from_subtree(node, BstDirection::Left);
            if pred == self.nil {
                self.link(node, dummy, BstDirection::Left);
            } else {
                self.link(pred, dummy, BstDirection::Right);
            }
        }

        let mut parent = self.arena[dummy].parent;

        loop {
            if parent == self.nil {
                break;
            }
            self.rotate(parent, dummy);
            parent = self.arena[dummy].parent;
        }

        let left = self.arena[dummy][BstDirection::Left];
        let right = self.arena[dummy][BstDirection::Right];

        self.arena[left].parent = self.nil;
        self.arena[right].parent = self.nil;
        self.init_dummy(dummy);

        if left == self.nil {
            return (None, Some(NodeIndex(right)));
        }
        if right == self.nil {
            return (Some(NodeIndex(left)), None);
        }

        (Some(NodeIndex(left)), Some(NodeIndex(right)))
    }

    fn split_all(&mut self, node: NodeIndex, size_hint: Option<usize>) -> Vec<NodeIndex> {
        let nodes: Vec<NodeIndex> = match size_hint {
            Some(s) => BinaryPreOrderIndices::with_capacity(self, node, s).collect(),
            None => BinaryPreOrderIndices::new(self, node).collect(),
        };

        for n in &nodes {
            self.arena[n.index()].level = 1;
            self.arena[n.index()].parent = self.nil;
            self.arena[n.index()][BstDirection::Left] = self.nil;
            self.arena[n.index()][BstDirection::Right] = self.nil;
            self.arena[n.index()].subweight = self.arena[n.index()].weight;
        }

        nodes
    }

    fn append(&mut self, node_u: NodeIndex, node_v: NodeIndex) -> Option<NodeIndex> {
        let root_v = self.root(node_v).map_or(self.nil, |r| r.index());
        let root_u = self.root(node_u).map_or(self.nil, |r| r.index());

        if root_u == self.nil {
            if root_v == self.nil {
                return None;
            } else {
                return Some(NodeIndex(root_v));
            }
        } else if root_v == self.nil {
            return Some(NodeIndex(root_u));
        }

        let mut dir = BstDirection::Right;
        let mut dest = root_u;
        let mut src = root_v;

        if self.arena[root_u].level < self.arena[root_v].level {
            dir = BstDirection::Left;
            dest = root_v;
            src = root_u;
        }

        let target_level = self.arena[src].level;
        let mut parent = self.nil;
        let mut child = dest;
        let other_dir = dir.other();

        loop {
            if self.arena[child].level == target_level {
                break;
            }
            parent = child;
            child = self.arena[parent][dir];
        }

        self.unlink(parent, child, dir);

        let dummy = self.jdummy;
        self.init_dummy(dummy);

        self.arena[dummy].level = target_level;
        self.link(dummy, child, other_dir);
        self.link(dummy, src, dir);
        self.link(parent, dummy, dir);

        child = dummy;
        parent = self.arena[child].parent;

        loop {
            self.update_weights(child);
            child = self.skew_node(child);
            self.split_node(child);

            if parent == self.nil {
                break;
            }

            child = parent;
            parent = self.arena[child].parent;
        }
        let root = self.isolate(dummy);
        self.init_dummy(dummy);
        Some(NodeIndex(root))
    }
}

impl<V, W> Traversable<V> for WeightedAaForest<V, W>
where
    V: ValueType,
    W: WeightType,
{
    fn root(&self, node: NodeIndex) -> Option<NodeIndex> {
        let node = node.index();
        if !self.is_valid_index(node) {
            return None;
        }
        let mut child = node;
        let mut parent = self.arena[child].parent;
        loop {
            if parent == self.nil {
                break;
            }
            child = parent;
            parent = self.arena[child].parent;
        }
        Some(NodeIndex(child))
    }

    fn value(&self, node: NodeIndex) -> Option<&V> {
        let node = node.index();
        if node <= self.sdummy {
            return None;
        }
        self.arena.get(node).map(|n| &n.value)
    }

    fn value_mut(&mut self, node: NodeIndex) -> Option<&mut V> {
        let node = node.index();
        if node <= self.sdummy {
            return None;
        }
        self.arena.get_mut(node).map(|n| &mut n.value)
    }

    fn parent(&self, node: NodeIndex) -> Option<NodeIndex> {
        let node = node.index();
        match self.arena.get(node) {
            Some(n) => {
                let parent = n.parent;
                if parent <= self.sdummy {
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
            if child <= self.sdummy {
                return None;
            }
            return Some(NodeIndex(child));
        }
        None
    }

    fn child_count(&self, node: NodeIndex) -> usize {
        let node = node.index();
        if self.arena.contains(node) {
            if node > self.sdummy {
                return 2;
            }
        }
        0
    }

    fn node_count(&self) -> usize {
        self.arena.len() - 3
    }
}

impl<V, W> OrderedTree for WeightedAaForest<V, W>
where
    V: ValueType,
    W: WeightType,
{
    fn sub_predecessor(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(
            WeightedAaForest::next_from_subtree,
            node.index(),
            BstDirection::Left,
        ).map(NodeIndex)
    }

    fn sub_successor(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(
            WeightedAaForest::next_from_subtree,
            node.index(),
            BstDirection::Right,
        ).map(NodeIndex)
    }

    fn predecessor(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(WeightedAaForest::next, node.index(), BstDirection::Left)
            .map(NodeIndex)
    }

    fn successor(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(WeightedAaForest::next, node.index(), BstDirection::Right)
            .map(NodeIndex)
    }

    fn first(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(WeightedAaForest::extreme, node.index(), BstDirection::Left)
            .map(NodeIndex)
    }

    fn last(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(WeightedAaForest::extreme, node.index(), BstDirection::Right)
            .map(NodeIndex)
    }

    fn is_smaller(&self, node_u: NodeIndex, node_v: NodeIndex) -> bool {
        let node_u = node_u.index();
        let node_v = node_v.index();
        if !self.is_valid_index(node_u) || !self.is_valid_index(node_v) || node_u == node_v {
            return false;
        }

        let (root_u, height_u) = self.root_and_height(node_u);
        let (root_v, height_v) = self.root_and_height(node_v);

        if root_u != root_v || root_u == self.nil {
            return false;
        }

        let path_u = self.directions_to_root(node_u, height_u);
        let path_v = self.directions_to_root(node_v, height_v);

        let mut i = 0;
        let mut mask = 1;

        loop {
            if (i >= height_u) || (i >= height_v) || ((path_u & mask) != (path_v & mask)) {
                break;
            }
            i += 1;
            mask <<= 1;
        }
        if (i < height_u) && ((path_u & mask) == 0) || (i < height_v) && ((path_v & mask) != 0) {
            return true;
        }
        false
    }
}

impl<V, W> WeightedTree<W> for WeightedAaForest<V, W>
where
    V: ValueType,
    W: WeightType,
{
    fn set_weight(&mut self, node: NodeIndex, weight: W) {
        let node = node.index();
        assert!(self.is_valid_index(node));
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

    fn weight(&self, node: NodeIndex) -> Option<&W> {
        if node.index() > self.sdummy {
            self.arena.get(node.index()).map(|n| &n.weight)
        } else {
            None
        }
    }

    fn subweight(&self, node: NodeIndex) -> Option<&W> {
        if node.index() > self.sdummy {
            self.arena.get(node.index()).map(|n| &n.subweight)
        } else {
            None
        }
    }

    fn adjust_weight(&mut self, node: NodeIndex, f: &Fn(&mut W)) {
        let node = node.index();
        assert!(self.is_valid_index(node));
        f(&mut self.arena[node].weight);
        let mut parent = node;
        loop {
            if parent == self.nil {
                break;
            }
            self.update_weights(parent);
            parent = self.arena[parent].parent;
        }
    }
}

impl<'slf, V, W> Values<'slf, V> for WeightedAaForest<V, W>
    where
        V: 'slf + ValueType,
        W: WeightType,
{
    fn values(&'slf self) -> Box<Iterator<Item=(NodeIndex, &'slf V)> + 'slf> {
        Box::new(
            self.arena
                .iter()
                .filter(move |n| n.0 > self.sdummy)
                .map(move |(i, n)| (NodeIndex(i), &n.value)),
        )
    }
}

impl<V, W> Index<NodeIndex> for WeightedAaForest<V, W>
where
    V: ValueType,
    W: WeightType,
{
    type Output = V;
    fn index(&self, index: NodeIndex) -> &V {
        &self.arena[index.index()].value
    }
}

impl<V, W> IndexMut<NodeIndex> for WeightedAaForest<V, W>
where
    V: ValueType,
    W: WeightType,
{
    fn index_mut(&mut self, index: NodeIndex) -> &mut V {
        &mut self.arena[index.index()].value
    }
}

impl<V, W> Tgf for WeightedAaForest<V, W>
where
    V: ValueType,
    W: WeightType,
{
    fn to_tgf(&self) -> String {
        let mut nodes = String::from("");
        let mut edges = String::from("");
        let iter = self.arena.iter();
        for (index, node) in iter {
            nodes.push_str(format!("{}", index).as_str());
            if index == self.nil {
                nodes.push_str(" [K = NIL");
            } else if index == self.jdummy || index == self.sdummy {
                nodes.push_str(" [K = DUMMY");
            } else {
                nodes.push_str(" [K = ");
                nodes.push_str(format!("{:?}", node.value).as_str());
            }

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
