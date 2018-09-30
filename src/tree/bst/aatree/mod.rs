//!
//! `AaTree<K, V>` is an unweighted balanced binary search tree data structure.
//!
use slab;
use std::cmp::Ordering;
use std::iter::empty;
use std::mem::swap;
use std::ops::{Index, IndexMut};
use tree::bst::{BinarySearchTree, BstDirection, OrderedTree};
use tree::traversal::{BinaryInOrder, BinaryInOrderIndices, Traversable};
use types::{Keys, KeyType, NodeIndex, Tgf, Values, ValueType};

#[cfg(test)]
mod tests;

#[derive(Clone, Debug)]
struct Node<K, V>
where
    K: KeyType,
    V: ValueType,
{
    key: K,
    value: V,
    level: usize,
    parent: usize,
    children: [usize; 2],
}

impl<K, V> Node<K, V>
where
    K: KeyType,
    V: ValueType,
{
    fn new() -> Self {
        Node {
            key: K::default(),
            value: V::default(),
            level: 0,
            parent: 0,
            children: [0, 0],
        }
    }

    fn new_leaf(key: K, value: V) -> Self {
        Node {
            key,
            value,
            level: 1,
            parent: 0,
            children: [0, 0],
        }
    }
}

impl<K, V> Index<BstDirection> for Node<K, V>
where
    K: KeyType,
    V: ValueType,
{
    type Output = usize;
    fn index(&self, index: BstDirection) -> &usize {
        &self.children[index as usize]
    }
}

impl<K, V> IndexMut<BstDirection> for Node<K, V>
where
    K: KeyType,
    V: ValueType,
{
    fn index_mut(&mut self, index: BstDirection) -> &mut usize {
        &mut self.children[index as usize]
    }
}

impl<K, V> Index<usize> for Node<K, V>
where
    K: KeyType,
    V: ValueType,
{
    type Output = usize;
    fn index(&self, index: usize) -> &usize {
        &self.children[index as usize]
    }
}

impl<K, V> IndexMut<usize> for Node<K, V>
where
    K: KeyType,
    V: ValueType,
{
    fn index_mut(&mut self, index: usize) -> &mut usize {
        &mut self.children[index as usize]
    }
}

/// `AaTree<K, V>` is a balanced binary search tree data structure. Its tree nodes
/// are held in a [memory arena][1] and are addressed through their associated `NodeIndex`.
///
/// The balancing method for maintaining a tree height of log(n) where n is the number nodes
/// in the tree is described here: [AA tree][2].
///
/// `AaTree` is parameterized over:
///
/// - Search keys of type `K`, where `K` must implement the trait [`KeyType`][3]
/// - Associated values of type `V`, where `V` must implement the trait [`ValueType`][4]
///
/// The usage of `AaTree` resembles that of [`BTreeMap`][5] from the standard library:
///
/// ```
/// use std::collections::BTreeMap;
/// use outils::prelude::*;
///
/// let mut btreemap = BTreeMap::new();
/// let mut aatree = AaTree::new(10);
///
/// btreemap.insert("DE", "Germany");
/// btreemap.insert("FR", "France");
/// btreemap.insert("IT", "Italy");
///
/// aatree.insert("DE", "Germany");
/// aatree.insert("FR", "France");
/// aatree.insert("IT", "Italy");
///
/// assert_eq!(btreemap.get(&"DE"), Some(&"Germany"));
/// assert_eq!(aatree.get(&"DE"), Some(&"Germany"));
///
/// assert_eq!(btreemap.remove(&"FR"), Some("France"));
/// assert_eq!(aatree.remove(&"FR"), Some("France"));
///
/// assert_eq!(btreemap.get(&"FR"), None);
/// assert_eq!(aatree.get(&"FR"), None);
/// ```
///
/// For most use cases, it is recommended to simply use `BTreeMap`, as it is considerably
/// faster (appr. 50%). However, if information on parent and child relations between tree nodes,
/// or custom traversal of the tree as such, are needed, `AaTree` has an advantage over `BTreeMap`.
///
/// [1]: https://en.wikipedia.org/wiki/Region-based_memory_management
/// [2]: https://en.wikipedia.org/wiki/AA_tree
/// [3]: types/trait.KeyType.html
/// [4]: ../../../types/trait.ValueType.html
/// [5]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html
///
#[derive(Clone, Debug)]
pub struct AaTree<K, V>
where
    K: KeyType,
    V: ValueType,
{
    arena: slab::Slab<Node<K, V>>,
    root: usize,
    nil: usize,
}

impl<K, V> AaTree<K, V>
where
    K: KeyType,
    V: ValueType,
{
    /// Construct a new empty `AaTree` with an initial capacity of `size`.
    pub fn new(size: usize) -> Self {
        let mut a = slab::Slab::with_capacity(size + 1);
        let n = a.insert(Node::new());

        AaTree {
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

    fn apply(
        &self,
        f: fn(&AaTree<K, V>, usize, BstDirection) -> usize,
        node: usize,
        dir: BstDirection,
    ) -> Option<usize> {
        if self.arena.contains(node) {
            let ret = f(self, node, dir);
            if ret == self.nil {
                return None;
            }
            return Some(ret);
        }
        None
    }
}

impl<K, V> BinarySearchTree<K, V> for AaTree<K, V>
where
    K: KeyType,
    V: ValueType,
{
    /// Inserts a key-value pair into the `AaTree`. If the tree did not have this `key` present, `None`
    /// is returned. If the tree **did** have this `key` present, the value is updated, and the old
    /// value is returned. Note that in this situation, the key is left unchanged.
    ///
    /// ```
    /// use outils::prelude::*;
    ///
    /// let mut aatree = AaTree::new(10);
    ///
    /// assert_eq!(aatree.insert("KEY-1", "VALUE-1"), None);
    /// assert_eq!(aatree.insert("KEY-2", "VALUE-2"), None);
    /// assert_eq!(aatree.insert("KEY-1", "VALUE-3"), Some("VALUE-1"));
    /// assert_eq!(aatree.get(&"KEY-1"), Some(&"VALUE-3"));
    /// assert_eq!(aatree.get(&"KEY-2"), Some(&"VALUE-2"));
    /// ```
    fn insert(&mut self, key: K, value: V) -> Option<V> {
        if self.root == self.nil {
            self.root = self.arena.insert(Node::new_leaf(key, value));
            return None;
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
                    let mut old_value = value;
                    swap(&mut self.arena[parent].value, &mut old_value);
                    return Some(old_value);
                }
            }

            if child == self.nil {
                child = self.arena.insert(Node::new_leaf(key, value));
                self.link(parent, child, dir);
                break;
            }

            parent = child;
        }

        loop {
            child = self.skew_node(child);
            child = self.split_node(child);
            child = self.arena[child].parent;
            if child == self.nil {
                break;
            }
        }
        None
    }

    /// Removes a `key` from the tree if present, in this case returning the associated value.
    ///
    /// ```
    /// use outils::prelude::*;
    ///
    /// let mut aatree = AaTree::new(10);
    /// aatree.insert("KEY-1", "VALUE-1");
    /// assert_eq!(aatree.remove(&"KEY-1"), Some("VALUE-1"));
    /// assert_eq!(aatree.remove(&"KEY-2"), None);
    /// ```
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

    /// Returns an immutable reference to the associated value of the specified `key`.
    fn get(&self, key: &K) -> Option<&V> {
        self.find_node(key).map(move |node| &self.arena[node].value)
    }

    /// Returns a mutable reference to the associated value of the specified `key`.
    fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        self.find_node(key)
            .map(move |node| &mut self.arena[node].value)
    }

    /// Returns the index of the tree node holding the specified `key`.
    fn index(&self, key: &K) -> Option<NodeIndex> {
        self.find_node(key).map(NodeIndex)
    }

    /// Returns `true` if the map contains a value for the specified `key`.
    fn contains_key(&self, key: &K) -> bool {
        self.find_node(key).is_some()
    }

    /// Returns the  key held by the tree node indexed by `node`.
    ///
    /// ```
    /// use outils::prelude::*;
    ///
    /// let mut aatree = AaTree::new(10);
    /// aatree.insert("KEY-1", "VALUE-1");
    /// let index = aatree.index(&"KEY-1").expect("KEY-1 should be present");
    /// assert_eq!(aatree.key(index), Some(&"KEY-1"));
    /// ```
    fn key(&self, node: NodeIndex) -> Option<&K> {
        let node = node.index();
        if node == self.nil {
            return None;
        }
        self.arena.get(node).map(|n| &n.key)
    }
}

impl<K, V> Traversable<V> for AaTree<K, V>
where
    K: KeyType,
    V: ValueType,
{
    /// Returns the index of the root node of the `AaTree`. Since the tree can only have one root
    /// the parameter `node` is not used.
    ///
    /// ```
    /// use outils::prelude::*;
    ///
    /// let mut aatree = AaTree::new(10);
    /// assert_eq!(aatree.root(NodeIndex(0)), None); // The parameter to root() doesn't matter!
    /// aatree.insert("KEY-1", "VALUE-1");
    ///
    /// // The solitary key in the tree must be the root
    /// let index = aatree.index(&"KEY-1").expect("KEY-1 should be present");
    ///
    /// assert_eq!(aatree.root(index), Some(index));
    /// assert_eq!(aatree.root(NodeIndex(0)), Some(index)); // The parameter to root() doesn't matter!
    /// ```
    fn root(&self, _node: NodeIndex) -> Option<NodeIndex> {
        if self.root == self.nil {
            return None;
        }
        Some(NodeIndex(self.root))
    }

    /// Immutably access the value stored in the `AaTree` indexed by `node`.
    fn value(&self, node: NodeIndex) -> Option<&V> {
        let node = node.index();
        if node == self.nil {
            return None;
        }
        self.arena.get(node).map(|n| &n.value)
    }

    /// Mutably access the value stored in the `AaTree` indexed by `node`.
    fn value_mut(&mut self, node: NodeIndex) -> Option<&mut V> {
        let node = node.index();
        if node == self.nil {
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
                if parent == self.nil {
                    return None;
                }
                Some(NodeIndex(parent))
            }
            None => None,
        }
    }

    /// Returns the index of the child node at position `pos` of  the tree node indexed by `node`.
    ///
    /// Note that a binary search tree node will always have two children, i.e. that even if the
    /// left child (`pos == 0`) is empty, the right child (`pos == 1`) might contain a value.
    /// In case of a leaf node, both children will be empty:
    ///
    /// ```
    /// use outils::prelude::*;
    ///
    /// let mut aatree = AaTree::new(10);
    /// aatree.insert(1, "1");
    /// aatree.insert(2, "2");
    ///
    /// // At this point, the AA algorithm has not had to rotate the tree, so that
    /// // the key `2` will be the right child of the key `1`:
    ///
    /// let parent = aatree.index(&1).expect("Key '1' should be present");
    /// assert_eq!(aatree.child(parent, 0), None);
    /// assert_eq!(aatree.child(parent, 1), aatree.index(&2));
    /// ```
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

    /// Returns the number of child nodes of the tree node indexed by `node`.
    ///
    /// Note that a binary search tree node will always have two children, i.e. that even if the
    /// left child is empty, the right child might contain a value.
    /// In case of a leaf node, both children will be empty, but the number of (empty) children
    /// will still be 2:
    ///
    /// ```
    /// use outils::prelude::*;
    ///
    /// let mut aatree = AaTree::new(10);
    /// aatree.insert(1, "1");
    /// aatree.insert(2, "2");
    ///
    /// // At this point, the AA algorithm has not had to rotate the tree, so that
    /// // the key `2` will be the right child of the key `1`:
    ///
    /// let parent = aatree.index(&1).expect("Key '1' should be present");
    /// let child = aatree.index(&2).expect("Key '2' should be present");
    ///
    /// assert_eq!(aatree.child_count(parent), 2);
    /// assert_eq!(aatree.child_count(child), 2);
    /// assert_eq!(aatree.child_count(NodeIndex(999)), 0); // Invalid index => no children
    /// ```
    fn child_count(&self, node: NodeIndex) -> usize {
        let node = node.index();
        if self.arena.contains(node) && node != self.nil {
            return 2;
        }
        0
    }

    /// Returns the total number of tree nodes of the tree `self`.
    fn node_count(&self) -> usize {
        self.arena.len() - 1
    }
}

impl<K, V> OrderedTree for AaTree<K, V>
where
    K: KeyType,
    V: ValueType,
{
    /// Returns the biggest node of the left subtree of the tree node indexed by `node`.
    ///
    /// ```
    /// use outils::prelude::*;            // The resulting tree is shown below:
    ///                                    //
    /// let mut aatree = AaTree::new(10);  //       -- (3) --
    ///                                    //      /         \
    /// for i in 0..7 {                    //    (1)         (5)
    ///     aatree.insert(i, i);           //   /   \       /   \
    /// }                                  // (0)   (2)    (4)   (6)
    ///
    /// let n2 = aatree.index(&2).expect("Key '2' should be present");
    /// let n3 = aatree.index(&3).expect("Key '3' should be present");
    /// let n4 = aatree.index(&4).expect("Key '4' should be present");
    ///
    /// assert_eq!(aatree.sub_predecessor(n3), Some(n2)); // 2 is biggest key in left subtree of 3.
    /// assert_eq!(aatree.sub_predecessor(n4), None);     // 4 is a leaf and thus has no subtrees.'
    /// ```
    fn sub_predecessor(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(AaTree::next_from_subtree, node.index(), BstDirection::Left)
            .map(NodeIndex)
    }

    /// Returns the smallest node of the right subtree of the tree node indexed by `node`.
    ///
    /// Usage is analogous to [`sub_predecessor`](#method.sub_predecessor)
    fn sub_successor(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(AaTree::next_from_subtree, node.index(), BstDirection::Right)
            .map(NodeIndex)
    }

    /// Returns the biggest node of the whole tree which is smaller than the tree node
    /// indexed by `node`.
    ///
    /// ```
    /// use outils::prelude::*;            // The resulting tree is shown below:
    ///                                    //
    /// let mut aatree = AaTree::new(10);  //       -- (3) --
    ///                                    //      /         \
    /// for i in 0..7 {                    //    (1)         (5)
    ///     aatree.insert(i, i);           //   /   \       /   \
    /// }                                  // (0)   (2)    (4)   (6)
    ///
    /// let n0 = aatree.index(&0).expect("Key '0' should be present");
    /// let n3 = aatree.index(&3).expect("Key '3' should be present");
    /// let n4 = aatree.index(&4).expect("Key '4' should be present");
    ///
    /// assert_eq!(aatree.predecessor(n4), Some(n3)); // 3 is the biggest key of the whole tree
    ///                                               // smaller than 4.
    /// assert_eq!(aatree.predecessor(n0), None);     // 0 is globally the smallest key of the
    ///                                               // whole tree and thus has no predecessor.
    /// ```
    fn predecessor(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(AaTree::next, node.index(), BstDirection::Left)
            .map(NodeIndex)
    }

    /// Returns the smallest node of the whole tree which is bigger than the tree node
    /// indexed by `node`.
    ///
    /// Usage is analogous to [`predecessor`](#method.predecessor)
    fn successor(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(AaTree::next, node.index(), BstDirection::Right)
            .map(NodeIndex)
    }

    /// Returns the smallest node of the left subtree of the tree node indexed by `node`.
    ///
    /// ```
    /// use outils::prelude::*;            // The resulting tree is shown below:
    ///                                    //
    /// let mut aatree = AaTree::new(10);  //       -- (3) --
    ///                                    //      /         \
    /// for i in 0..7 {                    //    (1)         (5)
    ///     aatree.insert(i, i);           //   /   \       /   \
    /// }                                  // (0)   (2)    (4)   (6)
    ///
    /// let n0 = aatree.index(&0).expect("Key '0' should be present");
    /// let n1 = aatree.index(&1).expect("Key '1' should be present");
    /// let n3 = aatree.index(&3).expect("Key '3' should be present");
    ///
    /// assert_eq!(aatree.first(n3), Some(n0));  // 0 is the smallest key of the left subtree of 3
    /// assert_eq!(aatree.first(n1), Some(n0));  // 0 is the smallest key of the left subtree of 1
    /// ```
    fn first(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(AaTree::extreme, node.index(), BstDirection::Left)
            .map(NodeIndex)
    }

    /// Returns the biggest node of the right subtree of the tree node indexed by `node`.
    ///
    /// Usage is analogous to [`first`](#method.first)
    fn last(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.apply(AaTree::extreme, node.index(), BstDirection::Right)
            .map(NodeIndex)
    }

    /// Returns `true` if the tree node indexed by `node_u` is smaller than the tree node
    /// indexed by `node_v`. Otherwise, and in particular if one of the specified indices
    /// is invalid, `false` is returned.
    ///
    /// **Panics** if the path to the root from either of the tree nodes to be compared contains
    /// more than 64 nodes. This is because the directions (i.e. left or right) on the path are
    /// encoded in a bitmap of type `u64`. In practice it is **next to impossible** for this method to
    /// panic because the number of tree nodes needs to be close to 2^64 for the above condition to occur.
    ///
    /// ```
    /// use outils::prelude::*;            // The resulting tree is shown below:
    ///                                    //
    /// let mut aatree = AaTree::new(10);  //       -- (3) --
    ///                                    //      /         \
    /// for i in 0..7 {                    //    (1)         (5)
    ///     aatree.insert(i, i);           //   /   \       /   \
    /// }                                  // (0)   (2)    (4)   (6)
    ///
    /// let n0 = aatree.index(&0).expect("Key '0' should be present");
    /// let n1 = aatree.index(&1).expect("Key '1' should be present");
    /// let n3 = aatree.index(&3).expect("Key '3' should be present");
    ///
    /// assert!(aatree.is_smaller(n0, n3));
    /// assert!(!aatree.is_smaller(n3, n1));
    /// ```
    fn is_smaller(&self, node_u: NodeIndex, node_v: NodeIndex) -> bool {
        let node_u = node_u.index();
        let node_v = node_v.index();
        if node_u == self.nil
            || !self.arena.contains(node_u)
            || node_v == self.nil
            || !self.arena.contains(node_v)
            {
            return false;
        }
        self.arena[node_u].key < self.arena[node_v].key
    }
}

impl<'slf, K, V> Keys<'slf, K> for AaTree<K, V>
where
    K: 'slf + KeyType,
    V: ValueType,
{
    /// Returns a boxed iterator over the search keys and their corresponding
    /// tree node indices held by `self`. The keys are returned in the order
    /// of the search keys.
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

impl<'slf, K, V> Values<'slf, V> for AaTree<K, V>
where
    K: KeyType,
    V: 'slf + ValueType,
{
    /// Returns a boxed iterator over the stored values and their corresponding
    /// tree node indices held by `self`. The keys are returned in the order
    /// of the corresponding search keys.
    fn values(&'slf self) -> Box<Iterator<Item=(NodeIndex, &'slf V)> + 'slf> {
        if self.root == self.nil {
            return Box::new(empty::<(NodeIndex, &'slf V)>());
        }
        Box::new(BinaryInOrder::new(self, NodeIndex(self.root)))
    }
}

impl<K, V> Index<NodeIndex> for AaTree<K, V>
where
    K: KeyType,
    V: ValueType,
{
    type Output = V;
    fn index(&self, index: NodeIndex) -> &V {
        &self.arena[index.index()].value
    }
}

impl<K, V> IndexMut<NodeIndex> for AaTree<K, V>
where
    K: KeyType,
    V: ValueType,
{
    fn index_mut(&mut self, index: NodeIndex) -> &mut V {
        &mut self.arena[index.index()].value
    }
}

impl<K, V> Tgf for AaTree<K, V>
where
    K: KeyType,
    V: ValueType,
{
    fn to_tgf(&self) -> String {
        let mut nodes = String::from("");
        let mut edges = String::from("");
        let iter = self.arena.iter();
        for (index, node) in iter {
            nodes.push_str(format!("{}", index).as_str());
            nodes.push_str(" [K = ");
            nodes.push_str(format!("{:?}", node.key).as_str());
            nodes.push_str(", V = ");
            nodes.push_str(format!("{:?}", node.value).as_str());
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
