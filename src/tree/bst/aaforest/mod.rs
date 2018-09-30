//!
//! `AaForest<V>` is an unweighted balanced binary forest data structure.
//!
use slab;
use std::ops::{Index, IndexMut};
use tree::bst::{BalancedBinaryForest, BstDirection, OrderedTree};
use tree::traversal::{BinaryPreOrderIndices, Traversable};
use types::{NodeIndex, Tgf, Values, ValueType};

#[cfg(test)]
mod tests;

#[derive(Debug, Clone)]
struct Node<V>
where
    V: ValueType,
{
    value: V,
    level: usize,
    parent: usize,
    children: [usize; 2],
}

impl<V> Node<V>
where
    V: ValueType,
{
    fn new() -> Self {
        Node {
            value: V::default(),
            level: 0,
            parent: 0,
            children: [0, 0],
        }
    }

    fn new_leaf(value: V) -> Self {
        Node {
            value,
            level: 1,
            parent: 0,
            children: [0, 0],
        }
    }
}

impl<V> Index<BstDirection> for Node<V>
where
    V: ValueType,
{
    type Output = usize;
    fn index(&self, index: BstDirection) -> &usize {
        &self.children[index as usize]
    }
}

impl<V> IndexMut<BstDirection> for Node<V>
where
    V: ValueType,
{
    fn index_mut(&mut self, index: BstDirection) -> &mut usize {
        &mut self.children[index as usize]
    }
}

impl<V> Index<usize> for Node<V>
where
    V: ValueType,
{
    type Output = usize;
    fn index(&self, index: usize) -> &usize {
        &self.children[index as usize]
    }
}

impl<V> IndexMut<usize> for Node<V>
where
    V: ValueType,
{
    fn index_mut(&mut self, index: usize) -> &mut usize {
        &mut self.children[index as usize]
    }
}

/// `AaForest<V>` is a data structure for holding balanced binary trees. Its tree nodes
/// are held in a [memory arena][1] and are addressed through their associated `NodeIndex`.
///
/// `AaForest` is parameterized over:
/// - Associated values of type `V`, where `V` must implement the trait [`ValueType`][2]
///
/// The balancing method for maintaining a tree height of log(n) where n is the number nodes
/// in the tree is described here: [AA tree][3].
///
/// Forest trees can be joined and split as required by the provided operations, which will
/// also take care of the re-balancing of the trees. The in-order of the forest trees implies an
/// ordered sequence of values - this order does not depend on the order traits of the type `V`
/// (i.e. [`std::cmp::Ord`][4]) but solely on the in-order of the nodes which is under the control
/// of the user (see the documentation of [`split`](#method.split) and [`append`](#method.append)).
///
/// ```
/// use outils::prelude::*;
/// use outils::tree::traversal::BinaryInOrderValues;
/// let mut aaforest = AaForest::new(10);
///
/// // Insert values into the forest - each value will be a single-node tree in the forest.
/// let n1 = aaforest.insert(1);
/// let n2 = aaforest.insert(2);
/// let n3 = aaforest.insert(3);
///
/// // Link the single-node trees, constructing the in-order sequence 1,2,3.
/// aaforest.append(n1, n2);
/// aaforest.append(n2, n3);
///
/// let seq: Vec<&usize> = BinaryInOrderValues::new(&aaforest, n1).collect();
/// assert_eq!(seq, vec![&1, &2, &3]);
/// ```
/// [1]: https://en.wikipedia.org/wiki/Region-based_memory_management
/// [2]: ../../../types/trait.ValueType.html
/// [3]: https://en.wikipedia.org/wiki/AA_tree
/// [4]: https://doc.rust-lang.org/std/cmp/trait.Ord.html
///
#[derive(Clone, Debug)]
pub struct AaForest<V>
where
    V: ValueType,
{
    arena: slab::Slab<Node<V>>,
    nil: usize,
    jdummy: usize,
    sdummy: usize,
}

impl<V> AaForest<V>
where
    V: ValueType,
{
    /// Construct a new empty `AaForest` with an initial capacity of `size`.
    pub fn new(size: usize) -> Self {
        let mut a = slab::Slab::with_capacity(size + 3);
        let n = a.insert(Node::new());
        let dj = a.insert(Node::new());
        let ds = a.insert(Node::new());
        AaForest {
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
        }
        ret
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
        self.arena[dummy].parent = self.nil;
        self.arena[dummy][BstDirection::Left] = self.nil;
        self.arena[dummy][BstDirection::Right] = self.nil;
        self.arena[dummy].level = 1;
    }

    fn next_from_subtree(&self, node: usize, dir: BstDirection) -> usize {
        let mut parent = self.arena[node][dir];
        let other_dir = dir.other();
        loop {
            let child = self.arena[parent][other_dir];
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
                return parent;
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
        f: fn(&AaForest<V>, usize, BstDirection) -> usize,
        node: usize,
        dir: BstDirection,
    ) -> Option<usize> {
        if self.arena.contains(node) {
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
        let mut parent = self
            .append(NodeIndex(left), NodeIndex(at))
            .map_or(self.nil, |p| p.index());
        parent = self
            .append(NodeIndex(parent), NodeIndex(right))
            .map_or(self.nil, |p| p.index());
        parent
    }

    fn rotate(&mut self, parent: usize, child: usize) {
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

        let other_child = if child_dir == BstDirection::Right {
            let left = self.arena[parent][BstDirection::Left];
            self.unlink(parent, left, BstDirection::Left);
            self.join_at(parent, left, grandchild)
        } else {
            let right = self.arena[parent][BstDirection::Right];
            self.unlink(parent, right, BstDirection::Right);
            self.join_at(parent, grandchild, right)
        };
        self.link(grandparent, child, parent_dir);
        self.link(child, other_child, other_dir);
    }
}

impl<V> Traversable<V> for AaForest<V>
where
    V: ValueType,
{
    /// Returns the index of the root node of the tree containing the tree node indexed by `node`.
    /// In case of an invalid index, `None` is returned.
    fn root(&self, node: NodeIndex) -> Option<NodeIndex> {
        let node = node.index();
        if node <= self.sdummy || !self.arena.contains(node) {
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

    /// Immutably access the value stored in the tree node indexed by `node`.
    fn value(&self, node: NodeIndex) -> Option<&V> {
        let node = node.index();
        if node <= self.sdummy {
            return None;
        }
        self.arena.get(node).map(|n| &n.value)
    }

    /// Mutably access the value stored in the tree node indexed by `node`.
    fn value_mut(&mut self, node: NodeIndex) -> Option<&mut V> {
        let node = node.index();
        if node <= self.sdummy {
            return None;
        }
        self.arena.get_mut(node).map(|n| &mut n.value)
    }

    /// Returns the index of parent node tree node indexed by `node`.
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

    /// Returns the index of the child node at position `pos` of  the tree node indexed by `node`.
    ///
    /// Note that a binary tree node will always have two children, i.e. that even if the
    /// left child (`pos == 0`) is empty, the right child (`pos == 1`) might contain a value.
    /// In case of a leaf node, both children will be empty:
    ///
    /// ```
    /// use outils::prelude::*;
    ///
    /// let mut aaforest = AaForest::new(10);
    /// let n1 = aaforest.insert(1);
    /// let n2 = aaforest.insert(2);
    /// aaforest.append(n1, n2);
    ///
    /// // At this point, the AA algorithm has not had to rotate the tree, so that
    /// // `n2` will be the right child of `n1`:
    ///
    /// assert_eq!(aaforest.child(n1, 0), None);
    /// assert_eq!(aaforest.child(n1, 1), Some(n2));
    /// ```
    fn child(&self, node: NodeIndex, pos: usize) -> Option<NodeIndex> {
        let node = node.index();
        if let Some(n) = self.arena.get(node) {
            if pos > 1 {
                return None;
            }
            let child = n[pos];
            if child <= self.sdummy {
                return None;
            }
            return Some(NodeIndex(child));
        }
        None
    }

    /// Returns the number of child nodes of the tree node indexed by `node`.
    ///
    /// Note that a binary tree node will always have two children, i.e. that even if the
    /// left child is empty, the right child might contain a value.
    /// In case of a leaf node, both children will be empty, but the number of (empty) children
    /// will still be 2:
    ///
    /// ```
    /// use outils::prelude::*;
    ///
    /// let mut aaforest = AaForest::new(10);
    /// let n1 = aaforest.insert(1);
    /// let n2 = aaforest.insert(2);
    /// aaforest.append(n1, n2);
    ///
    /// // At this point, the AA algorithm has not had to rotate the tree, so that
    /// // `n2` will be the right child of `n1`:
    ///
    /// assert_eq!(aaforest.child_count(n1), 2);
    /// assert_eq!(aaforest.child_count(n2), 2);
    /// assert_eq!(aaforest.child_count(NodeIndex(999)), 0); // Invalid index => no children
    /// ```
    fn child_count(&self, node: NodeIndex) -> usize {
        let node = node.index();
        if self.arena.contains(node) && node > self.sdummy {
            return 2;
        }
        0
    }

    /// Returns the total number of tree nodes of the forest trees in `self`.
    fn node_count(&self) -> usize {
        self.arena.len() - 3
    }
}

impl<V> OrderedTree for AaForest<V>
where
    V: ValueType,
{
    /// Returns the biggest node of the left subtree of the tree node indexed by `node`.
    ///
    /// ```
    /// use outils::prelude::*;                // The resulting tree is shown below:
    ///                                        //
    /// let mut aaforest = AaForest::new(10);  //       -- (3) --
    ///                                        //      /         \
    /// let mut indices = Vec::new();          //    (1)         (5)
    /// indices.push(aaforest.insert(0));      //   /   \       /   \
    ///                                        // (0)   (2)    (4)   (6)
    /// for i in 1..7 {
    ///     indices.push(aaforest.insert(i));
    ///     aaforest.append(indices[i-1], indices[i]);
    /// }
    ///
    /// // 2 is biggest key in left subtree of 3.
    /// assert_eq!(aaforest.sub_predecessor(indices[3]), Some(indices[2]));
    /// // 4 is a leaf and thus has no subtrees.
    /// assert_eq!(aaforest.sub_predecessor(indices[4]), None);
    /// ```
    fn sub_predecessor(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(
            AaForest::next_from_subtree,
            node.index(),
            BstDirection::Left,
        )
            .map(NodeIndex)
    }

    /// Returns the smallest node of the right subtree of the tree node indexed by `node`.
    ///
    /// Usage is analogous to [`sub_predecessor`](#method.sub_predecessor)
    fn sub_successor(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(
            AaForest::next_from_subtree,
            node.index(),
            BstDirection::Right,
        )
            .map(NodeIndex)
    }

    /// Returns the biggest node of the whole tree which is smaller than the tree node
    /// indexed by `node`.
    ///
    /// ```
    /// use outils::prelude::*;                // The resulting tree is shown below:
    ///                                        //
    /// let mut aaforest = AaForest::new(10);  //       -- (3) --
    ///                                        //      /         \
    /// let mut indices = Vec::new();          //    (1)         (5)
    /// indices.push(aaforest.insert(0));      //   /   \       /   \
    ///                                        // (0)   (2)    (4)   (6)
    /// for i in 1..7 {
    ///     indices.push(aaforest.insert(i));
    ///     aaforest.append(indices[i-1], indices[i]);
    /// }
    ///
    /// // 3 is the biggest key of the whole tree smaller than 4.
    /// assert_eq!(aaforest.predecessor(indices[4]), Some(indices[3]));
    /// // 0 is globally the smallest key of the whole tree and thus has no predecessor.
    /// assert_eq!(aaforest.predecessor(indices[0]), None);
    /// ```
    fn predecessor(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(AaForest::next, node.index(), BstDirection::Left)
            .map(NodeIndex)
    }

    /// Returns the smallest node of the whole tree which is bigger than the tree node
    /// indexed by `node`.
    ///
    /// Usage is analogous to [`predecessor`](#method.predecessor)
    fn successor(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(AaForest::next, node.index(), BstDirection::Right)
            .map(NodeIndex)
    }

    /// Returns the smallest node of the left subtree of the tree node indexed by `node`.
    ///
    /// ```
    /// use outils::prelude::*;                // The resulting tree is shown below:
    ///                                        //
    /// let mut aaforest = AaForest::new(10);  //       -- (3) --
    ///                                        //      /         \
    /// let mut indices = Vec::new();          //    (1)         (5)
    /// indices.push(aaforest.insert(0));      //   /   \       /   \
    ///                                        // (0)   (2)    (4)   (6)
    /// for i in 1..7 {
    ///     indices.push(aaforest.insert(i));
    ///     aaforest.append(indices[i-1], indices[i]);
    /// }
    ///
    /// // 0 is the smallest key of the left subtree of 3
    /// assert_eq!(aaforest.first(indices[3]), Some(indices[0]));
    /// // 0 is the smallest key of the left subtree of 1
    /// assert_eq!(aaforest.first(indices[1]), Some(indices[0]));
    /// ```
    fn first(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(AaForest::extreme, node.index(), BstDirection::Left)
            .map(NodeIndex)
    }

    /// Returns the biggest node of the right subtree of the tree node indexed by `node`.
    ///
    /// Usage is analogous to [`first`](#method.first)
    fn last(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(AaForest::extreme, node.index(), BstDirection::Right)
            .map(NodeIndex)
    }

    /// Returns `true` if the tree node indexed by `node_u` is smaller than the tree node
    /// indexed by `node_v`. Otherwise, and in particular if one of the specified indices
    /// is invalid, or if the nodes do not belong to the same forest tree, `false` is returned.
    ///
    /// **Panics** if the path to the root from either of the tree nodes to be compared contains
    /// more than 64 nodes. This is because the directions (i.e. left or right) on the path are
    /// encoded in a bitmap of type `u64`. In practice it is **next to impossible** for this method to
    /// panic because the number of tree nodes needs to be close to 2^64 for the above condition to occur.
    ///
    /// ```
    /// use outils::prelude::*;                // The resulting tree is shown below:
    ///                                        //
    /// let mut aaforest = AaForest::new(10);  //       -- (3) --
    ///                                        //      /         \
    /// let mut indices = Vec::new();          //    (1)         (5)
    /// indices.push(aaforest.insert(0));      //   /   \       /   \
    ///                                        // (0)   (2)    (4)   (6)
    /// for i in 1..7 {
    ///     indices.push(aaforest.insert(i));
    ///     aaforest.append(indices[i-1], indices[i]);
    /// }
    ///
    /// assert!(aaforest.is_smaller(indices[0], indices[3]));
    /// assert!(!aaforest.is_smaller(indices[3], indices[1]));
    /// ```
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

impl<V> BalancedBinaryForest<V> for AaForest<V>
where
    V: ValueType,
{
    // Insert a new singleton node containing `value` into the forest.
    fn insert(&mut self, value: V) -> NodeIndex {
        NodeIndex(self.arena.insert(Node::new_leaf(value)))
    }

    /// Removes the tree node indexed by `node` from the tree if present, in this case returning
    /// the associated value.
    ///
    /// ```
    /// use outils::prelude::*;                             // The resulting tree is shown below:
    /// use outils::tree::traversal::BinaryInOrderValues;   //
    ///                                                     //       -- (3) --
    /// let mut aaforest = AaForest::new(10);               //      /         \
    ///                                                     //    (1)         (5)
    /// let mut indices = Vec::new();                       //   /   \       /   \
    /// indices.push(aaforest.insert(0));                   // (0)   (2)    (4)   (6)
    ///
    /// for i in 1..7 {
    ///     indices.push(aaforest.insert(i));
    ///     aaforest.append(indices[i-1], indices[i]);
    /// }
    ///
    /// assert_eq!(aaforest.remove(indices[5]), Some(5));
    /// let seq: Vec<&usize> = BinaryInOrderValues::new(&aaforest, indices[0]).collect();
    /// assert_eq!(seq, vec![&0, &1, &2, &3, &4, &6]);
    /// ```
    fn remove(&mut self, node: NodeIndex) -> Option<V> {
        let node = node.index();
        if node <= self.sdummy {
            return None;
        }

        self.arena.get(node)?;
        self.isolate(node);
        Some(self.arena.remove(node).value)
    }

    /// Splits the sequence of tree nodes represented by the forest tree containing the tree node
    /// indexed by `node`.
    ///
    /// If `dir == BstDirection::Left`, `node` will index the last tree node of the left sequence,
    /// while if `dir == BstDirection::Right`, `node` will index the first tree node of the right
    /// sequence (both with respect to in-order). The roots of the resulting sequences will be
    /// returned as a tuple.
    ///
    /// ```
    /// use outils::prelude::*;                             // The resulting trees are shown below:
    /// use outils::tree::traversal::BinaryInOrderValues;   //
    ///                                                     //       -- (3) --
    /// let mut aaforest1 = AaForest::new(10);              //      /         \
    /// let mut aaforest2 = AaForest::new(10);              //    (1)         (5)
    ///                                                     //   /   \       /   \
    /// let mut indices1 = Vec::new();                      // (0)   (2)    (4)   (6)
    /// indices1.push(aaforest1.insert(0));
    /// let mut indices2 = Vec::new();
    /// indices2.push(aaforest2.insert(0));
    ///
    /// for i in 1..7 {
    ///     indices1.push(aaforest1.insert(i));
    ///     aaforest1.append(indices1[i-1], indices1[i]);
    ///     indices2.push(aaforest2.insert(i));
    ///     aaforest2.append(indices2[i-1], indices2[i]);
    /// }
    ///
    /// // Split the tree at 3 and keep 3 as part of the left (i.e. _smaller_) tree.
    /// let result1 = aaforest1.split(indices1[3], BstDirection::Left);
    /// match(result1) {
    ///     (Some(left), Some(right)) => {
    ///         let seq_left: Vec<&usize> = BinaryInOrderValues::new(&aaforest1, left).collect();
    ///         assert_eq!(seq_left, vec![&0, &1, &2, &3]);
    ///         let seq_right: Vec<&usize> = BinaryInOrderValues::new(&aaforest1, right).collect();
    ///         assert_eq!(seq_right, vec![&4, &5, &6]);
    ///     }
    ///     _ => {
    ///         panic!("3 was neither first nor last, so the returned tuple should be (Some, Some)")
    ///     }
    /// }
    ///
    /// // Split the tree at 3 and keep 3 as part of the right (i.e. _bigger_) tree.
    /// let result2 = aaforest2.split(indices2[3], BstDirection::Right);
    /// match(result2) {
    ///     (Some(left), Some(right)) => {
    ///         let seq_left: Vec<&usize> = BinaryInOrderValues::new(&aaforest2, left).collect();
    ///         assert_eq!(seq_left, vec![&0, &1, &2]);
    ///         let seq_right: Vec<&usize> = BinaryInOrderValues::new(&aaforest2, right).collect();
    ///         assert_eq!(seq_right, vec![&3, &4, &5, &6]);
    ///     }
    ///     _ => {
    ///         panic!("3 was neither first nor last, so the returned tuple should be (Some, Some)");
    ///     }
    /// }
    /// ```
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

        self.unlink(dummy, left, BstDirection::Left);
        self.unlink(dummy, right, BstDirection::Right);
        self.arena[dummy].level = 0;

        if left == self.nil {
            return (None, Some(NodeIndex(right)));
        }
        if right == self.nil {
            return (Some(NodeIndex(left)), None);
        }

        (Some(NodeIndex(left)), Some(NodeIndex(right)))
    }

    /// Splits the whole sequence of tree nodes represented by the forest tree containing the tree
    /// node indexed by `node` into singleton (i.e. sole leaf) nodes.
    ///
    /// If the tree nodes to be split is known beforehand, it can be specified optionally as
    /// the `size_hint` of the returned `Vec` containing the split tree nodes.
    ///
    /// Generally, this operation will be much faster than calling `split` on each node of the
    /// sequence separately, the reason being that no re-balancing is necessary when it is known
    /// beforehand that every tree node will be split.
    ///
    /// ```
    /// use outils::prelude::*;                // The resulting tree is shown below:
    ///                                        //
    /// let mut aaforest = AaForest::new(10);  //       -- (3) --
    ///                                        //      /         \
    /// let mut indices = Vec::new();          //    (1)         (5)
    /// indices.push(aaforest.insert(0));      //   /   \       /   \
    ///                                        // (0)   (2)    (4)   (6)
    /// for i in 1..7 {
    ///     indices.push(aaforest.insert(i));
    ///     aaforest.append(indices[i-1], indices[i]);
    /// }
    ///
    /// let split_nodes = aaforest.split_all(indices[0], Some(7));
    /// assert_eq!(split_nodes.len(), indices.len());
    ///
    /// // After splitting the forest tree, every one of its former nodes should be a singleton:
    /// for i in 0..7 {
    ///     assert!(split_nodes.contains(&indices[i]));
    ///     assert_eq!(aaforest.parent(indices[i]), None);
    ///     assert_eq!(aaforest.child(indices[i], 0), None);
    ///     assert_eq!(aaforest.child(indices[i], 1), None);
    /// }
    /// ```
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
        }
        nodes
    }

    /// Concatenate the sequences of tree nodes represented by the forest trees containing the
    /// tree nodes indexed by `node_u` and `node_v`, respectively.
    ///
    /// With respect to in-order, the former sequence will represent the _smaller_ part of the
    /// new sequence, the latter sequence the _bigger_ part. The root of the resulting sequence will
    /// be returned.
    ///
    /// ```
    /// use outils::prelude::*;
    /// use outils::tree::traversal::BinaryInOrderValues;
    /// let mut aaforest = AaForest::new(10);
    ///
    /// // Insert values into the forest - each value will be a single-node tree in the forest.
    /// let mut indices = Vec::new();
    /// for i in 0..7 {
    ///     indices.push(aaforest.insert(i));
    /// }
    ///
    /// // Construct the _smaller_ tree, containing the in-order sequence 0,1,2,3
    /// let mut left = indices[0];
    /// left = aaforest.append(left, indices[1]).expect("Result should not be None");
    /// left = aaforest.append(left, indices[2]).expect("Result should not be None");
    /// left = aaforest.append(left, indices[3]).expect("Result should not be None");
    ///
    /// { // Restrict scope of the borrow of `aaforest`.
    ///     let seq: Vec<&usize> = BinaryInOrderValues::new(&aaforest, left).collect();
    ///     assert_eq!(seq, vec![&0, &1, &2, &3]);
    /// }
    ///
    /// // Construct the _bigger_ tree, containing the in-order sequence 4,5,6
    /// let mut right = indices[4];
    /// right = aaforest.append(right, indices[5]).expect("Result should not be None");
    /// right = aaforest.append(right, indices[6]).expect("Result should not be None");
    ///
    /// { // Restrict scope of the borrow of `aaforest`.
    ///     let seq: Vec<&usize> = BinaryInOrderValues::new(&aaforest, right).collect();
    ///     assert_eq!(seq, vec![&4, &5, &6]);
    /// }
    ///
    /// // Link left and right, constructing the in-order sequence 0,1,2,3,4,5,6.
    /// let root = aaforest.append(left, right).expect("Result should not be None");
    /// let seq: Vec<&usize> = BinaryInOrderValues::new(&aaforest, root).collect();
    /// assert_eq!(seq, vec![&0, &1, &2, &3, &4, &5, &6]);
    /// ```
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

        let dir = if self.arena[root_u].level < self.arena[root_v].level {
            BstDirection::Left
        } else {
            BstDirection::Right
        };

        let dest = if self.arena[root_u].level < self.arena[root_v].level {
            root_v
        } else {
            root_u
        };

        let src = if self.arena[root_u].level < self.arena[root_v].level {
            root_u
        } else {
            root_v
        };

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

impl<'slf, V> Values<'slf, V> for AaForest<V>
    where
        V: 'slf + ValueType,
{
    /// Returns a boxed iterator over the stored values and their corresponding
    /// tree node indices held by `self`. The values are not returned in any
    /// particular order.
    fn values(&'slf self) -> Box<Iterator<Item=(NodeIndex, &'slf V)> + 'slf> {
        Box::new(
            self.arena
                .iter()
                .filter(move |n| n.0 > self.sdummy)
                .map(move |(i, n)| (NodeIndex(i), &n.value)),
        )
    }
}

impl<V> Index<NodeIndex> for AaForest<V>
where
    V: ValueType,
{
    type Output = V;
    fn index(&self, index: NodeIndex) -> &V {
        &self.arena[index.index()].value
    }
}

impl<V> IndexMut<NodeIndex> for AaForest<V>
where
    V: ValueType,
{
    fn index_mut(&mut self, index: NodeIndex) -> &mut V {
        &mut self.arena[index.index()].value
    }
}

impl<V> Tgf for AaForest<V>
where
    V: ValueType,
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
