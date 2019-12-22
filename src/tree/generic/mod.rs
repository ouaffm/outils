//!
//! Generic, general purpose tree data structures.
//!
pub use self::error::TreeError;
use slab;
use std::ops::{Index, IndexMut};
use crate::tree::traversal::Traversable;
use crate::types::{Children, DefaultIndexType, IndexType, NodeIndex, Tgf, Values, ValueType};

#[cfg(test)]
mod tests;

pub mod error;

/// This trait defines the fundamental operations of a generic forest.
pub trait GenericForest<V, Ix = DefaultIndexType>: Traversable<V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    /// Inserts `value` into the forest as a new root node and return the assigned `NodeIndex`.
    fn insert(&mut self, value: V) -> NodeIndex<Ix>;

    /// Inserts `value` into the forest as a new node. which will be the last child of the
    /// node indexed by `parent`. If the operation has been completed successfully, the
    /// index of the new child is returned. Otherwise, in particular if `parent` is not a
    /// valid node index, an error is returned.
    fn insert_child(
        &mut self,
        parent: NodeIndex<Ix>,
        value: V,
    ) -> Result<NodeIndex<Ix>, TreeError<Ix>>;

    /// Inserts `value` into the forest as a new node. which will be a child of the
    /// node indexed by `parent` at the position specified by `pos`. If `pos` is greater than or
    /// equal to the number of children of `parent`, the new child will be the new last child.
    /// If the operation has been completed successfully, the index of the new child is returned.
    /// Otherwise, if `parent` is not a valid node index, an error is returned.
    fn insert_child_at(
        &mut self,
        parent: NodeIndex<Ix>,
        pos: usize,
        value: V,
    ) -> Result<NodeIndex<Ix>, TreeError<Ix>>;

    /// Removes the tree node indexed by `node`, returning its content in case of a valid index.
    /// If the removed node has children, they will become children of the parent of the removed node,
    /// replacing the removed node. If the removed node has no parent, its children will become roots.
    fn remove(&mut self, node: NodeIndex<Ix>) -> Result<V, TreeError<Ix>>;

    /// Removes the tree node indexed by `node` and its subtree, returning the contents of the
    /// removed nodes in case of a valid index. The returned values will be collected in pre-order.
    fn remove_subtree(&mut self, node: NodeIndex<Ix>)
                      -> Result<Vec<(NodeIndex, V)>, TreeError<Ix>>;

    /// Adds the root node `child` as the new last child of the node indexed by `parent`. If the operation has
    /// been completed successfully, `Ok(())` is returned. If the forest has not been changed, an error
    /// is returned. This will be the case if:
    ///
    /// - the node indexed by `child` is not a tree root, i.e. has a parent.
    /// - the node indexed by `parent` is a node in the tree rooted in `child`.
    /// - either `parent` or `child` is not a valid node index.
    fn set_as_child(
        &mut self,
        parent: NodeIndex<Ix>,
        child: NodeIndex<Ix>,
    ) -> Result<(), TreeError<Ix>>;

    /// Adds the root node `child` as a child of the node indexed by `parent` at the position specified
    /// by `pos`. If `pos` is greater than or equal to the number of children of `parent`, the new
    /// child will be the new last child. If the operation has been completed successfully, `Ok(())`
    /// is returned. If the forest has not been changed, an error is returned. This will be the case if:
    ///
    /// - the node indexed by `child` is not a tree root, i.e. has a parent.
    /// - the node indexed by `parent` is a node in the tree rooted in `child`.
    /// - either `parent` or `child` is not a valid node index.
    fn set_as_child_at(
        &mut self,
        parent: NodeIndex<Ix>,
        child: NodeIndex<Ix>,
        pos: usize,
    ) -> Result<(), TreeError<Ix>>;

    /// Removes the node indexed by `node` as a child of its parent, thus making it a new root
    /// node of the forest. If the operation has been completed successfully, `Ok(())` is returned.
    /// If `node` is not a valid not index, an error is returned.
    fn remove_as_child(&mut self, node: NodeIndex<Ix>) -> Result<(), TreeError<Ix>>;
}

#[derive(Debug, Clone)]
struct Node<V>
    where
        V: ValueType,
{
    value: V,
    child_count: usize,
    context: NodeContext,
}

impl<V> Node<V>
    where
        V: ValueType,
{
    fn new(value: V) -> Self {
        Node {
            value,
            child_count: 0,
            context: NodeContext::new(),
        }
    }
}

#[derive(Copy, Clone, Debug)]
struct NodeContext {
    parent: Option<NodeIndex>,
    first_child: Option<NodeIndex>,
    last_child: Option<NodeIndex>,
    prev_sibling: Option<NodeIndex>,
    next_sibling: Option<NodeIndex>,
}

impl NodeContext {
    fn new() -> Self {
        NodeContext {
            parent: None,
            first_child: None,
            last_child: None,
            prev_sibling: None,
            next_sibling: None,
        }
    }
}

struct ChildIterator<'slf, V>
    where
        V: 'slf + ValueType,
{
    forest: &'slf Forest<V>,
    current: Option<NodeIndex>,
}

impl<'slf, V> ChildIterator<'slf, V>
    where
        V: 'slf + ValueType,
{
    fn new(forest: &'slf Forest<V>, node: NodeIndex) -> Self {
        ChildIterator {
            forest,
            current: forest
                .arena
                .get(node.index())
                .and_then(|n| n.context.first_child),
        }
    }
}

impl<'slf, V> Iterator for ChildIterator<'slf, V>
    where
        V: 'slf + ValueType,
{
    type Item = NodeIndex;
    fn next(&mut self) -> Option<NodeIndex> {
        let ret = self.current;
        match ret {
            Some(n) => {
                self.current = self.forest.arena[n.index()].context.next_sibling;
                ret
            }
            None => None,
        }
    }
}

/// `Forest<V>` is a general purpose data structure for holding a forest of trees. Its tree nodes
/// are held in a [memory arena][1] and are addressed through their associated `NodeIndex`.
///
/// `Forest` is parameterized over:
/// - Associated values of type `V`, where `V` must implement the trait [`ValueType`][2]
///
/// The tree nodes of the forest are organized in a first child/next-sibling representation,
/// augmented by last child/previous sibling links. In other words, the children of tree node are
/// maintained in doubly linked list, where the head and tail of the list are the first and last
/// child values of the children's parent node.
///
/// Therefore, no allocations and re-allocations are necessary when adding children to nodes.
/// Re-allocation will only take place if the underlying memory arena has reached its capacity.
///
/// However, care must be taken when accessing a child node by its position, that is, by using
/// the method [`child(node, pos)`][3] of the [`Traversal`][4] trait, because to access a child by
/// its position in the list, the list has to be iterated from the beginning. Using access by
/// position is therefore not very efficient. This caveat also applies to the generic traversal
/// iterators provided by the [`traversal`][5] module, which are build on access by position.
///
/// In order to iterate over the children of node, the trait [`Children`][6] is available.
///
/// To illustrate the above explations see the following example:
///
/// ```
/// use outils::prelude::*;
/// use outils::tree::traversal::GeneralDfsValues;
/// let mut forest = Forest::new(10);
///
/// // Create a root with 9 child nodes.
/// let root = forest.insert(9);
/// for i in (0..9) {
///     forest.insert_child(root, i);
/// }
///
/// // Inefficient iteration:
/// for pos in (0..9) {
///     let index = forest.child(root, pos).expect("Should not fail here!"); // Inefficient!
///     let value = forest.value(index).expect("Should not fail here!");
///     assert_eq!(*value, pos);
/// }
///
/// // Also inefficient is using the provided, generic traversals:
/// let seq: Vec<&usize> = GeneralDfsValues::new(&forest, root).collect(); // Will use child()!
/// assert_eq!(seq, vec![&9, &0, &1, &2, &3, &4, &5, &6, &7, &8]);
///
/// // Efficient iteration:
/// let mut pos = 0;
/// for child in forest.children(root) {
///     let value = forest.value(child).expect("Should not fail here!");
///     assert_eq!(*value, pos);
///     pos += 1;
/// }
/// ```
///
/// [1]: https://en.wikipedia.org/wiki/Region-based_memory_management
/// [2]: ../../types/trait.ValueType.html
/// [3]: ../traversal/trait.Traversable.html#tymethod.child
/// [4]: ../traversal/trait.Traversable.html
/// [5]: ../traversal/index.html
/// [6]: ../../types/trait.Children.html
#[derive(Clone, Debug)]
pub struct Forest<V>
    where
        V: ValueType,
{
    arena: slab::Slab<Node<V>>,
    roots: Vec<NodeIndex>,
}

impl<V> Forest<V>
    where
        V: ValueType,
{
    /// Construct a new empty `Forest` with an initial capacity of `size`.
    pub fn new(size: usize) -> Self {
        Forest {
            arena: slab::Slab::with_capacity(size),
            roots: Vec::new(),
        }
    }

    /// Returns the index of the first child node of the tree node indexed by `node`. If the node
    /// has no children or `node` is not a valid index, `None` is returned.
    ///
    /// ```
    /// use outils::prelude::*;
    ///
    /// let mut tree = Forest::new(10);
    /// let root = tree.insert(1);
    /// let first_child = tree.insert_child(root, 2).expect("Should not fail here");
    /// let second_child = tree.insert_child(root, 3).expect("Should not fail here");
    ///
    /// assert_eq!(tree.first_child(root), Some(first_child));
    /// ```
    pub fn first_child(&self, parent: NodeIndex) -> Option<NodeIndex> {
        self.arena
            .get(parent.index())
            .and_then(|p| p.context.first_child)
    }

    /// Returns the index of the last child node of the tree node indexed by `node`. If the node
    /// has no children or `node` is not a valid index, `None` is returned.
    ///
    /// ```
    /// use outils::prelude::*;
    ///
    /// let mut tree = Forest::new(10);
    /// let root = tree.insert(1);
    /// let first_child = tree.insert_child(root, 2).expect("Should not fail here");
    /// let second_child = tree.insert_child(root, 3).expect("Should not fail here");
    ///
    /// assert_eq!(tree.last_child(root), Some(second_child));
    /// ```
    pub fn last_child(&self, parent: NodeIndex) -> Option<NodeIndex> {
        self.arena
            .get(parent.index())
            .and_then(|p| p.context.last_child)
    }

    /// Returns the index of the previous sibling node of the tree node indexed by `node`. If the
    /// node is the first child of its parent or `node` is not a valid index, `None` is returned.
    ///
    /// ```
    /// use outils::prelude::*;
    ///
    /// let mut tree = Forest::new(10);
    /// let root = tree.insert(1);
    /// let first_child = tree.insert_child(root, 2).expect("Should not fail here");
    /// let second_child = tree.insert_child(root, 3).expect("Should not fail here");
    ///
    /// assert_eq!(tree.prev_sibling(second_child), Some(first_child));
    /// ```
    pub fn prev_sibling(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.arena
            .get(node.index())
            .and_then(|n| n.context.prev_sibling)
    }

    /// Returns the index of the next sibling node of the tree node indexed by `node`. If the
    /// node is the last child of its parent or `node` is not a valid index, `None` is returned.
    ///
    /// ```
    /// use outils::prelude::*;
    ///
    /// let mut tree = Forest::new(10);
    /// let root = tree.insert(1);
    /// let first_child = tree.insert_child(root, 2).expect("Should not fail here");
    /// let second_child = tree.insert_child(root, 3).expect("Should not fail here");
    ///
    /// assert_eq!(tree.next_sibling(first_child), Some(second_child));
    /// ```
    pub fn next_sibling(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.arena
            .get(node.index())
            .and_then(|n| n.context.next_sibling)
    }

    /// Returns the list of root node indices of this forest. The values are not returned in any
    /// particular order.
    ///
    /// ```
    /// use outils::prelude::*;
    ///
    /// let mut tree = Forest::new(10);
    /// let first_root = tree.insert(1);
    /// let second_root = tree.insert(2);
    ///
    /// let roots = tree.roots();
    /// assert!(roots.contains(&first_root));
    /// assert!(roots.contains(&second_root));
    /// ```
    pub fn roots(&self) -> &Vec<NodeIndex> {
        &self.roots
    }
}

impl<'slf, V> Children<'slf> for Forest<V>
    where
        V: 'slf + ValueType,
{
    fn children(&'slf self, node: NodeIndex) -> Box<dyn Iterator<Item=NodeIndex> + 'slf> {
        Box::new(ChildIterator::new(self, node))
    }
}

impl<V> Index<NodeIndex> for Forest<V>
    where
        V: ValueType,
{
    type Output = V;
    fn index(&self, index: NodeIndex) -> &V {
        &self.arena[index.index()].value
    }
}

impl<V> IndexMut<NodeIndex> for Forest<V>
    where
        V: ValueType,
{
    fn index_mut(&mut self, index: NodeIndex) -> &mut V {
        &mut self.arena[index.index()].value
    }
}

impl<V> Traversable<V> for Forest<V>
    where
        V: ValueType,
{
    /// Returns the index of the root node of the tree containing the tree node indexed by `node`.
    fn root(&self, node: NodeIndex) -> Option<NodeIndex> {
        if let Some(_n) = self.arena.get(node.index()) {
            let mut child = node;
            while let Some(parent) = self.arena[child.index()].context.parent {
                child = parent;
            }
            return Some(child);
        }
        None
    }

    /// Immutably access the value stored in the tree node indexed by `node`.
    fn value(&self, node: NodeIndex) -> Option<&V> {
        self.arena.get(node.index()).map(|n| &n.value)
    }

    /// Mutably access the value stored in the tree node indexed by `node`.
    fn value_mut(&mut self, node: NodeIndex) -> Option<&mut V> {
        self.arena.get_mut(node.index()).map(|n| &mut n.value)
    }

    /// Returns the index of parent node tree node indexed by `node`.
    fn parent(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.arena.get(node.index()).and_then(|n| n.context.parent)
    }

    /// Returns the index of the child node at position `pos` of  the tree node indexed by `node`.
    fn child(&self, node: NodeIndex, pos: usize) -> Option<NodeIndex> {
        ChildIterator::new(self, node).nth(pos)
    }

    /// Returns the number of child nodes of the tree node indexed by `node`.
    fn child_count(&self, node: NodeIndex) -> usize {
        self.arena.get(node.index()).map_or(0, |n| n.child_count)
    }

    /// Returns the total number of tree nodes of the tree `self`.
    fn node_count(&self) -> usize {
        self.arena.len()
    }
}

impl<'slf, V> Values<'slf, V> for Forest<V>
    where
        V: 'slf + ValueType,
{
    /// Returns a boxed iterator over the stored values and their corresponding
    /// tree node indices held by `self`.
    fn values(&'slf self) -> Box<dyn Iterator<Item=(NodeIndex, &'slf V)> + 'slf> {
        Box::new(self.arena.iter().map(|(i, v)| (NodeIndex(i), &v.value)))
    }
}

impl<V> GenericForest<V> for Forest<V>
    where
        V: ValueType,
{
    /// Inserts `value` into the forest as a new root node and return the assigned `NodeIndex`.
    fn insert(&mut self, value: V) -> NodeIndex {
        let node = NodeIndex(self.arena.insert(Node::new(value)));
        self.roots.push(node);
        node
    }

    /// Inserts `value` into the forest as a new node. which will be the last child of the
    /// node indexed by `parent`. If the operation has been completed successfully, the
    /// index of the new child is returned. Otherwise, in particular if `parent` is not a
    /// valid node index, an error is returned.
    fn insert_child(&mut self, parent: NodeIndex, value: V) -> Result<NodeIndex, TreeError> {
        if !self.arena.contains(parent.index()) {
            return Err(TreeError::invalid_node_index("insert_child()", parent));
        }
        let child = NodeIndex(self.arena.insert(Node::new(value)));

        match self.arena[parent.index()].context.last_child {
            Some(last) => {
                self.arena[last.index()].context.next_sibling = Some(child);
                self.arena[parent.index()].context.last_child = Some(child);
                self.arena[child.index()].context.prev_sibling = Some(last);
            }
            None => {
                self.arena[parent.index()].context.first_child = Some(child);
                self.arena[parent.index()].context.last_child = Some(child);
            }
        }
        self.arena[child.index()].context.parent = Some(parent);
        self.arena[parent.index()].child_count += 1;
        Ok(child)
    }

    /// Inserts `value` into the forest as a new node. which will be a child of the
    /// node indexed by `parent` at the position specified by `pos`. If `pos` is greater than or
    /// equal to the number of children of `parent`, the new child will be the new last child.
    /// If the operation has been completed successfully, the index of the new child is returned.
    /// Otherwise, if `parent` is not a valid node index, an error is returned.
    fn insert_child_at(
        &mut self,
        parent: NodeIndex,
        pos: usize,
        value: V,
    ) -> Result<NodeIndex, TreeError> {
        if !self.arena.contains(parent.index()) {
            return Err(TreeError::invalid_node_index("insert_child_at()", parent));
        }
        let child = NodeIndex(self.arena.insert(Node::new(value)));

        let mut prev = None;
        let mut next = self.arena[parent.index()].context.first_child;
        let mut i = 0;

        while i < pos {
            match next {
                Some(n) => {
                    prev = next;
                    next = self.arena[n.index()].context.next_sibling;
                    i += 1;
                }
                None => {
                    break;
                }
            }
        }
        match (prev, next) {
            (None, Some(n)) => {
                self.arena[n.index()].context.prev_sibling = Some(child);
                self.arena[parent.index()].context.first_child = Some(child);
            }
            (Some(p), Some(n)) => {
                self.arena[n.index()].context.prev_sibling = Some(child);
                self.arena[p.index()].context.next_sibling = Some(child);
            }
            (Some(p), None) => {
                self.arena[p.index()].context.next_sibling = Some(child);
                self.arena[parent.index()].context.last_child = Some(child);
            }
            (None, None) => {
                self.arena[parent.index()].context.first_child = Some(child);
                self.arena[parent.index()].context.last_child = Some(child);
            }
        }
        self.arena[child.index()].context.parent = Some(parent);
        self.arena[child.index()].context.prev_sibling = prev;
        self.arena[child.index()].context.next_sibling = next;
        self.arena[parent.index()].child_count += 1;
        Ok(child)
    }

    /// Removes the tree node indexed by `node`, returning its content in case of a valid index.
    /// If the removed node has children, they will become children of the parent of the removed node,
    /// replacing the removed node. If the removed node has no parent, its children will become roots.
    fn remove(&mut self, node: NodeIndex) -> Result<V, TreeError> {
        if !self.arena.contains(node.index()) {
            return Err(TreeError::invalid_node_index("remove()", node));
        }

        let context = self.arena[node.index()].context;
        match context.parent {
            Some(parent) => {
                match (
                    context.first_child,
                    context.last_child,
                    context.prev_sibling,
                    context.next_sibling,
                ) {
                    (Some(first), Some(last), Some(prev), Some(next)) => {
                        self.arena[prev.index()].context.next_sibling = Some(first);
                        self.arena[next.index()].context.prev_sibling = Some(last);
                        self.arena[first.index()].context.prev_sibling = Some(prev);
                        self.arena[last.index()].context.next_sibling = Some(next);
                    }
                    (Some(first), Some(last), Some(prev), None) => {
                        self.arena[parent.index()].context.last_child = Some(last);
                        self.arena[first.index()].context.prev_sibling = Some(prev);
                        self.arena[prev.index()].context.next_sibling = Some(first);
                    }
                    (Some(first), Some(last), None, Some(next)) => {
                        self.arena[parent.index()].context.first_child = Some(first);
                        self.arena[last.index()].context.next_sibling = Some(next);
                        self.arena[next.index()].context.prev_sibling = Some(last);
                    }
                    (Some(first), Some(last), None, None) => {
                        self.arena[parent.index()].context.first_child = Some(first);
                        self.arena[parent.index()].context.last_child = Some(last);
                    }
                    (None, None, Some(prev), Some(next)) => {
                        self.arena[prev.index()].context.next_sibling = Some(next);
                        self.arena[next.index()].context.prev_sibling = Some(prev);
                    }

                    (None, None, Some(prev), None) => {
                        self.arena[parent.index()].context.last_child = Some(prev);
                        self.arena[prev.index()].context.next_sibling = None;
                    }

                    (None, None, None, Some(next)) => {
                        self.arena[parent.index()].context.first_child = Some(next);
                        self.arena[next.index()].context.prev_sibling = None;
                    }

                    (None, None, None, None) => {
                        self.arena[parent.index()].context.first_child = None;
                        self.arena[parent.index()].context.last_child = None;
                    }
                    _ => panic!("remove(): first and last child indices are incorrect"),
                }
                let mut child = self.arena[node.index()].context.first_child;
                while let Some(c) = child {
                    child = self.arena[c.index()].context.next_sibling;
                    self.arena[c.index()].context.parent = Some(parent);
                }
                self.arena[parent.index()].child_count -= 1;
                self.arena[parent.index()].child_count += self.arena[node.index()].child_count;
            }
            None => {
                self.roots.retain(|&r| r != node);
                let mut child = self.arena[node.index()].context.first_child;
                while let Some(c) = child {
                    child = self.arena[c.index()].context.next_sibling;
                    self.arena[c.index()].context.parent = None;
                    self.arena[c.index()].context.prev_sibling = None;
                    self.arena[c.index()].context.next_sibling = None;
                    self.roots.push(c);
                }
            }
        }
        Ok(self.arena.remove(node.index()).value)
    }

    /// Removes the tree node indexed by `node` and its subtree, returning the contents of the
    /// removed nodes in case of a valid index. The returned values will be collected in pre-order.
    fn remove_subtree(&mut self, node: NodeIndex) -> Result<Vec<(NodeIndex, V)>, TreeError> {
        if self.remove_as_child(node).is_err() {
            return Err(TreeError::invalid_node_index("remove_subtree()", node));
        }

        let mut stack = Vec::with_capacity(self.arena[node.index()].child_count + 1);
        let mut ret = Vec::with_capacity(stack.capacity());
        stack.push(node);
        while let Some(parent) = stack.pop() {
            let mut child = self.arena[parent.index()].context.last_child;
            while let Some(c) = child {
                stack.push(c);
                child = self.arena[c.index()].context.prev_sibling;
            }
            ret.push((parent, self.arena.remove(parent.index()).value));
        }
        self.roots.retain(|&r| r != node);
        Ok(ret)
    }

    /// Adds the root node `child` as the new last child of the node indexed by `parent`. If the operation has
    /// been completed successfully, `Ok(())` is returned. If the forest has not been changed, an error
    /// is returned. This will be the case if:
    ///
    /// - the node indexed by `child` is not a tree root, i.e. has a parent.
    /// - the node indexed by `parent` is a node in the tree rooted in `child`.
    /// - either `parent` or `child` is not a valid node index.
    fn set_as_child(&mut self, parent: NodeIndex, child: NodeIndex) -> Result<(), TreeError> {
        if !self.arena.contains(parent.index()) {
            return Err(TreeError::invalid_node_index("set_as_child()", parent));
        }
        if !self.arena.contains(child.index()) {
            return Err(TreeError::invalid_node_index("set_as_child()", child));
        }
        if self.arena[child.index()].context.parent.is_some() {
            return Err(TreeError::expected_root_node("set_as_child()", child));
        }
        if self.root(parent) == Some(child) {
            return Err(TreeError::expected_non_ancestor_node(
                "set_as_child()",
                parent,
                child,
            ));
        }

        match self.arena[parent.index()].context.last_child {
            Some(last) => {
                self.arena[last.index()].context.next_sibling = Some(child);
                self.arena[child.index()].context.prev_sibling = Some(last);
                self.arena[parent.index()].context.last_child = Some(child);
            }
            None => {
                self.arena[parent.index()].context.first_child = Some(child);
                self.arena[parent.index()].context.last_child = Some(child);
            }
        }
        self.arena[child.index()].context.parent = Some(parent);
        self.arena[parent.index()].child_count += 1;
        self.roots.retain(|&r| r != child);
        Ok(())
    }

    /// Adds the root node `child` as a child of the node indexed by `parent` at the position specified
    /// by `pos`. If `pos` is greater than or equal to the number of children of `parent`, the new
    /// child will be the new last child. If the operation has been completed successfully, `Ok(())`
    /// is returned. If the forest has not been changed, an error is returned. This will be the case if:
    ///
    /// - the node indexed by `child` is not a tree root, i.e. has a parent.
    /// - the node indexed by `parent` is a node in the tree rooted in `child`.
    /// - either `parent` or `child` is not a valid node index.
    fn set_as_child_at(
        &mut self,
        parent: NodeIndex,
        child: NodeIndex,
        pos: usize,
    ) -> Result<(), TreeError> {
        if !self.arena.contains(parent.index()) {
            return Err(TreeError::invalid_node_index("set_as_child_at()", parent));
        }
        if !self.arena.contains(child.index()) {
            return Err(TreeError::invalid_node_index("set_as_child_at()", child));
        }
        if self.arena[child.index()].context.parent.is_some() {
            return Err(TreeError::expected_root_node("set_as_child_at()", child));
        }
        if self.root(parent) == Some(child) {
            return Err(TreeError::expected_non_ancestor_node(
                "set_as_child_at()",
                parent,
                child,
            ));
        }

        let mut prev = None;
        let mut next = self.arena[parent.index()].context.first_child;
        let mut i = 0;

        while i < pos {
            match next {
                Some(n) => {
                    prev = next;
                    next = self.arena[n.index()].context.next_sibling;
                    i += 1;
                }
                None => {
                    break;
                }
            }
        }
        match (prev, next) {
            (None, Some(n)) => {
                self.arena[n.index()].context.prev_sibling = Some(child);
                self.arena[parent.index()].context.first_child = Some(child);
            }
            (Some(p), Some(n)) => {
                self.arena[n.index()].context.prev_sibling = Some(child);
                self.arena[p.index()].context.next_sibling = Some(child);
            }
            (Some(p), None) => {
                self.arena[p.index()].context.next_sibling = Some(child);
                self.arena[parent.index()].context.last_child = Some(child);
            }
            (None, None) => {
                self.arena[parent.index()].context.first_child = Some(child);
                self.arena[parent.index()].context.last_child = Some(child);
            }
        }
        self.arena[child.index()].context.parent = Some(parent);
        self.arena[child.index()].context.prev_sibling = prev;
        self.arena[child.index()].context.next_sibling = next;
        self.arena[parent.index()].child_count += 1;
        self.roots.retain(|&r| r != child);
        Ok(())
    }

    /// Removes the node indexed by `node` as a child of its parent, thus making it a new root
    /// node of the forest. If the operation has been completed successfully, `Ok(())` is returned.
    /// If `node` is not a valid not index, an error is returned.
    fn remove_as_child(&mut self, node: NodeIndex) -> Result<(), TreeError> {
        if !self.arena.contains(node.index()) {
            return Err(TreeError::invalid_node_index("remove_as_child()", node));
        }
        let context = self.arena[node.index()].context;

        if let Some(parent) = context.parent {
            match (context.prev_sibling, context.next_sibling) {
                (Some(prev), Some(next)) => {
                    self.arena[prev.index()].context.next_sibling = Some(next);
                    self.arena[next.index()].context.prev_sibling = Some(prev);
                }
                (Some(prev), None) => {
                    self.arena[prev.index()].context.next_sibling = None;
                    self.arena[parent.index()].context.last_child = Some(prev);
                }
                (None, Some(next)) => {
                    self.arena[next.index()].context.prev_sibling = None;
                    self.arena[parent.index()].context.first_child = Some(next);
                }
                (None, None) => {
                    self.arena[parent.index()].context.first_child = None;
                    self.arena[parent.index()].context.last_child = None;
                }
            }
            self.arena[parent.index()].child_count -= 1;
            self.roots.push(node);
        }
        self.arena[node.index()].context = NodeContext {
            parent: None,
            first_child: context.first_child,
            last_child: context.last_child,
            prev_sibling: None,
            next_sibling: None,
        };
        Ok(())
    }
}

impl<V> Tgf for Forest<V>
    where
        V: ValueType,
{
    fn to_tgf(&self) -> String {
        let mut nodes = String::from("");
        let mut edges = String::from("");
        let iter = self.arena.iter();
        for (index, node) in iter {
            nodes.push_str(format!("{}", index).as_str());
            nodes.push_str(" [K = ");
            nodes.push_str(format!("{}", index).as_str());
            nodes.push_str(", V = ");
            nodes.push_str(format!("{:?}", node.value).as_str());
            nodes.push_str("]\n");

            for child in self.children(NodeIndex(index)).enumerate() {
                edges.push_str(format!("{}", index).as_str());
                edges.push_str(" ");
                edges.push_str(format!("{}", child.1.index()).as_str());
                edges.push_str(" ");
                edges.push_str(format!("{}", child.0).as_str());
                edges.push_str("\n");
            }
        }
        nodes.push_str("#\n");
        nodes.push_str(edges.as_str());
        nodes
    }
}
