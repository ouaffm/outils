//! Tree traversal iterators over node indices, node values or both at the same time. In order for
//! a tree data structure to support these iterators, the `Traversable` trait must be implemented.
//!
//! Provided traversals are:
//!
//! - [Binary In-Order](https://en.wikipedia.org/wiki/Tree_traversal#In-order)
//! - [Binary Pre-Order](https://en.wikipedia.org/wiki/Tree_traversal#Pre-order)
//! - [Binary Post-Order](https://en.wikipedia.org/wiki/Tree_traversal#Post-order)
//! - [Depth-First Search](https://en.wikipedia.org/wiki/Tree_traversal#Generic_tree)
//! - [Breadth-First Search](https://en.wikipedia.org/wiki/Tree_traversal#Breadth-first_search)
//!
use std::collections::VecDeque;
use crate::types::{DefaultIndexType, IndexType, NodeIndex, ValueType};

#[cfg(test)]
mod tests;

/// This trait defines the interface for using the traversal iterators provided by this module.
pub trait Traversable<V, Ix = DefaultIndexType>
    where
        V: ValueType,
        Ix: IndexType,
{
    /// Returns the index of the root node of the tree containing the tree node indexed by `node`.
    fn root(&self, node: NodeIndex<Ix>) -> Option<NodeIndex<Ix>>;

    /// Immutably access the value stored in the tree node indexed by `node`.
    fn value(&self, node: NodeIndex<Ix>) -> Option<&V>;

    /// Mutably access the value stored in the tree node indexed by `node`.
    fn value_mut(&mut self, node: NodeIndex<Ix>) -> Option<&mut V>;

    /// Returns the index of parent node tree node indexed by `node`.
    fn parent(&self, node: NodeIndex<Ix>) -> Option<NodeIndex<Ix>>;

    /// Returns the index of the child node at position `pos` of  the tree node indexed by `node`.
    fn child(&self, node: NodeIndex<Ix>, pos: usize) -> Option<NodeIndex<Ix>>;

    /// Returns the number of child nodes of the tree node indexed by `node`.
    fn child_count(&self, node: NodeIndex<Ix>) -> usize;

    /// Returns the total number of tree nodes of the tree `self`.
    fn node_count(&self) -> usize;
}

/// Iterator over node indices in binary in-order
pub struct BinaryInOrderIndices<'tree, V, Ix = DefaultIndexType>
    where
        V: ValueType,
        Ix: IndexType,
{
    tree: &'tree dyn Traversable<V, Ix>,
    current: Option<NodeIndex<Ix>>,
    stack: Vec<NodeIndex<Ix>>,
    size_hint: (usize, Option<usize>),
}

/// Iterator over node contents in binary in-order
pub struct BinaryInOrderValues<'tree, V, Ix = DefaultIndexType>
    where
        V: ValueType,
        Ix: IndexType,
{
    iter: BinaryInOrderIndices<'tree, V, Ix>,
}

/// Iterator over node contents and the corresponding node indices in binary in-order
pub struct BinaryInOrder<'tree, V, Ix = DefaultIndexType>
    where
        V: ValueType,
        Ix: IndexType,
{
    iter: BinaryInOrderIndices<'tree, V, Ix>,
}

impl<'tree, V, Ix> BinaryInOrderIndices<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`.
    pub fn new(tree: &'tree dyn Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        let rt = tree.root(node);
        BinaryInOrderIndices {
            tree,
            current: rt,
            stack: Vec::new(),
            size_hint: (0, None),
        }
    }

    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`. The argument `stack_hint` indicates the height of the
    /// `Traversable` tree to be iterated over, such that the internal stack does not need to be
    /// re-allocated.
    pub fn with_capacity(
        tree: &'tree dyn Traversable<V, Ix>,
        node: NodeIndex<Ix>,
        size_hint: usize,
    ) -> Self {
        let rt = tree.root(node);
        let stack_hint = (size_hint as f64).log2().floor() as usize;
        BinaryInOrderIndices {
            tree,
            current: rt,
            stack: Vec::with_capacity(stack_hint),
            size_hint: (0, Some(size_hint)),
        }
    }
}

impl<'tree, V, Ix> Iterator for BinaryInOrderIndices<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    type Item = NodeIndex<Ix>;

    fn next(&mut self) -> Option<NodeIndex<Ix>> {
        while let Some(node) = self.current {
            self.stack.push(node);
            self.current = self.tree.child(node, 0);
        }
        let node = self.stack.pop();
        self.current = node.and_then(|n| self.tree.child(n, 1));
        node
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.size_hint
    }
}

impl<'tree, V, Ix> BinaryInOrderValues<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`
    pub fn new(tree: &'tree dyn Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        BinaryInOrderValues {
            iter: BinaryInOrderIndices::new(tree, node),
        }
    }

    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`. The argument `stack_hint` indicates the height of the
    /// `Traversable` tree to be iterated over, such that the internal stack does not need to be
    /// re-allocated.
    pub fn with_capacity(
        tree: &'tree dyn Traversable<V, Ix>,
        node: NodeIndex<Ix>,
        size_hint: usize,
    ) -> Self {
        BinaryInOrderValues {
            iter: BinaryInOrderIndices::with_capacity(tree, node, size_hint),
        }
    }
}

impl<'tree, V, Ix> Iterator for BinaryInOrderValues<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    type Item = &'tree V;

    fn next(&mut self) -> Option<&'tree V> {
        self.iter.next().and_then(|n| self.iter.tree.value(n))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint
    }
}

impl<'tree, V, Ix> BinaryInOrder<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`
    pub fn new(tree: &'tree dyn Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        BinaryInOrder {
            iter: BinaryInOrderIndices::new(tree, node),
        }
    }

    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`. The argument `stack_hint` indicates the height of the
    /// `Traversable` tree to be iterated over, such that the internal stack does not need to be
    /// re-allocated.
    pub fn with_capacity(
        tree: &'tree dyn Traversable<V, Ix>,
        node: NodeIndex<Ix>,
        size_hint: usize,
    ) -> Self {
        BinaryInOrder {
            iter: BinaryInOrderIndices::with_capacity(tree, node, size_hint),
        }
    }
}

impl<'tree, V, Ix> Iterator for BinaryInOrder<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    type Item = (NodeIndex<Ix>, &'tree V);

    fn next(&mut self) -> Option<(NodeIndex<Ix>, &'tree V)> {
        self.iter
            .next()
            .and_then(|n| self.iter.tree.value(n).map(|v| (n, v)))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// Iterator over node indices in binary pre-order
pub struct BinaryPreOrderIndices<'tree, V, Ix = DefaultIndexType>
    where
        V: ValueType,
        Ix: IndexType,
{
    tree: &'tree dyn Traversable<V, Ix>,
    stack: Vec<NodeIndex<Ix>>,
    size_hint: (usize, Option<usize>),
}

/// Iterator over node contents in binary pre-order
pub struct BinaryPreOrderValues<'tree, V, Ix = DefaultIndexType>
    where
        V: ValueType,
        Ix: IndexType,
{
    iter: BinaryPreOrderIndices<'tree, V, Ix>,
}

/// Iterator over node contents and the corresponding node indices in binary pre-order
pub struct BinaryPreOrder<'tree, V, Ix = DefaultIndexType>
    where
        V: ValueType,
        Ix: IndexType,
{
    iter: BinaryPreOrderIndices<'tree, V, Ix>,
}

impl<'tree, V, Ix> BinaryPreOrderIndices<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`
    pub fn new(tree: &'tree dyn Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        let mut v = Vec::new();
        if let Some(rt) = tree.root(node) {
            v.push(rt)
        }
        BinaryPreOrderIndices {
            tree,
            stack: v,
            size_hint: (0, None),
        }
    }

    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`. The argument `stack_hint` indicates the height of the
    /// `Traversable` tree to be iterated over, such that the internal stack does not need to be
    /// re-allocated.
    pub fn with_capacity(
        tree: &'tree dyn Traversable<V, Ix>,
        node: NodeIndex<Ix>,
        size_hint: usize,
    ) -> Self {
        let stack_hint = (size_hint as f64).log2().floor() as usize;
        let mut v = Vec::with_capacity(stack_hint);
        if let Some(rt) = tree.root(node) {
            v.push(rt);
        }
        BinaryPreOrderIndices {
            tree,
            stack: v,
            size_hint: (0, Some(size_hint)),
        }
    }
}

impl<'tree, V, Ix> Iterator for BinaryPreOrderIndices<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    type Item = NodeIndex<Ix>;

    fn next(&mut self) -> Option<NodeIndex<Ix>> {
        match self.stack.pop() {
            Some(n) => {
                if let Some(c) = self.tree.child(n, 1) {
                    self.stack.push(c);
                }
                if let Some(c) = self.tree.child(n, 0) {
                    self.stack.push(c);
                }
                Some(n)
            }
            None => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.size_hint
    }
}

impl<'tree, V, Ix> BinaryPreOrderValues<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`
    pub fn new(tree: &'tree dyn Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        BinaryPreOrderValues {
            iter: BinaryPreOrderIndices::new(tree, node),
        }
    }

    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`. The argument `stack_hint` indicates the height of the
    /// `Traversable` tree to be iterated over, such that the internal stack does not need to be
    /// re-allocated.
    pub fn with_capacity(
        tree: &'tree dyn Traversable<V, Ix>,
        node: NodeIndex<Ix>,
        size_hint: usize,
    ) -> Self {
        BinaryPreOrderValues {
            iter: BinaryPreOrderIndices::with_capacity(tree, node, size_hint),
        }
    }
}

impl<'tree, V, Ix> Iterator for BinaryPreOrderValues<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    type Item = &'tree V;

    fn next(&mut self) -> Option<&'tree V> {
        self.iter.next().and_then(|n| self.iter.tree.value(n))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'tree, V, Ix> BinaryPreOrder<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`
    pub fn new(tree: &'tree dyn Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        BinaryPreOrder {
            iter: BinaryPreOrderIndices::new(tree, node),
        }
    }

    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`. The argument `stack_hint` indicates the height of the
    /// `Traversable` tree to be iterated over, such that the internal stack does not need to be
    /// re-allocated.
    pub fn with_capacity(
        tree: &'tree dyn Traversable<V, Ix>,
        node: NodeIndex<Ix>,
        size_hint: usize,
    ) -> Self {
        BinaryPreOrder {
            iter: BinaryPreOrderIndices::with_capacity(tree, node, size_hint),
        }
    }
}

impl<'tree, V, Ix> Iterator for BinaryPreOrder<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    type Item = (NodeIndex<Ix>, &'tree V);

    fn next(&mut self) -> Option<(NodeIndex<Ix>, &'tree V)> {
        self.iter
            .next()
            .and_then(|n| self.iter.tree.value(n).map(|v| (n, v)))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// Iterator over node indices in binary post-order
pub struct BinaryPostOrderIndices<'tree, V, Ix = DefaultIndexType>
    where
        V: ValueType,
        Ix: IndexType,
{
    tree: &'tree dyn Traversable<V, Ix>,
    current: Option<NodeIndex<Ix>>,
    stack: Vec<NodeIndex<Ix>>,
    size_hint: (usize, Option<usize>),
}

/// Iterator over node contents in binary post-order
pub struct BinaryPostOrderValues<'tree, V, Ix = DefaultIndexType>
    where
        V: ValueType,
        Ix: IndexType,
{
    iter: BinaryPostOrderIndices<'tree, V, Ix>,
}

/// Iterator over node contents and the corresponding node indices in binary post-order
pub struct BinaryPostOrder<'tree, V, Ix = DefaultIndexType>
    where
        V: ValueType,
        Ix: IndexType,
{
    iter: BinaryPostOrderIndices<'tree, V, Ix>,
}

impl<'tree, V, Ix> BinaryPostOrderIndices<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`
    pub fn new(tree: &'tree dyn Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        let rt = tree.root(node);
        BinaryPostOrderIndices {
            tree,
            current: rt,
            stack: Vec::new(),
            size_hint: (0, None),
        }
    }

    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`. The argument `stack_hint` indicates the height of the
    /// `Traversable` tree to be iterated over, such that the internal stack does not need to be
    /// re-allocated.
    pub fn with_capacity(
        tree: &'tree dyn Traversable<V, Ix>,
        node: NodeIndex<Ix>,
        size_hint: usize,
    ) -> Self {
        let rt = tree.root(node);
        let stack_hint = (size_hint as f64).log2().floor() as usize;
        BinaryPostOrderIndices {
            tree,
            current: rt,
            stack: Vec::with_capacity(stack_hint),
            size_hint: (0, Some(size_hint)),
        }
    }
}

impl<'tree, V, Ix> Iterator for BinaryPostOrderIndices<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    type Item = NodeIndex<Ix>;

    fn next(&mut self) -> Option<NodeIndex<Ix>> {
        loop {
            if let Some(n) = self.current {
                if let Some(c) = self.tree.child(n, 1) {
                    self.stack.push(c);
                }
                self.stack.push(n);
                self.current = self.tree.child(n, 0);
                continue;
            }

            if let Some(n) = self.stack.pop() {
                if let Some(c1) = self.tree.child(n, 1) {
                    if let Some(c2) = self.stack.pop() {
                        if c1 == c2 {
                            self.stack.push(n);
                            self.current = Some(c2);
                        } else {
                            self.stack.push(c2);
                            return Some(n);
                        }
                    } else {
                        return Some(n);
                    }
                } else {
                    return Some(n);
                }
            } else {
                return None;
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.size_hint
    }
}

impl<'tree, V, Ix> BinaryPostOrderValues<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`
    pub fn new(tree: &'tree dyn Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        BinaryPostOrderValues {
            iter: BinaryPostOrderIndices::new(tree, node),
        }
    }

    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`. The argument `stack_hint` indicates the height of the
    /// `Traversable` tree to be iterated over, such that the internal stack does not need to be
    /// re-allocated.
    pub fn with_capacity(
        tree: &'tree dyn Traversable<V, Ix>,
        node: NodeIndex<Ix>,
        size_hint: usize,
    ) -> Self {
        BinaryPostOrderValues {
            iter: BinaryPostOrderIndices::with_capacity(tree, node, size_hint),
        }
    }
}

impl<'tree, V, Ix> Iterator for BinaryPostOrderValues<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    type Item = &'tree V;

    fn next(&mut self) -> Option<&'tree V> {
        self.iter.next().and_then(|n| self.iter.tree.value(n))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'tree, V, Ix> BinaryPostOrder<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`
    pub fn new(tree: &'tree dyn Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        BinaryPostOrder {
            iter: BinaryPostOrderIndices::new(tree, node),
        }
    }

    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`. The argument `stack_hint` indicates the height of the
    /// `Traversable` tree to be iterated over, such that the internal stack does not need to be
    /// re-allocated.
    pub fn with_capacity(
        tree: &'tree dyn Traversable<V, Ix>,
        node: NodeIndex<Ix>,
        size_hint: usize,
    ) -> Self {
        BinaryPostOrder {
            iter: BinaryPostOrderIndices::with_capacity(tree, node, size_hint),
        }
    }
}

impl<'tree, V, Ix> Iterator for BinaryPostOrder<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    type Item = (NodeIndex<Ix>, &'tree V);

    fn next(&mut self) -> Option<(NodeIndex<Ix>, &'tree V)> {
        self.iter
            .next()
            .and_then(|n| self.iter.tree.value(n).map(|v| (n, v)))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// Iterator over node indices in depth-first search order
pub struct GeneralDfsIndices<'tree, V, Ix = DefaultIndexType>
    where
        V: ValueType,
        Ix: IndexType,
{
    tree: &'tree dyn Traversable<V, Ix>,
    stack: Vec<NodeIndex<Ix>>,
    size_hint: (usize, Option<usize>),
}

/// Iterator over node contents in depth-first search order
pub struct GeneralDfsValues<'tree, V, Ix = DefaultIndexType>
    where
        V: ValueType,
        Ix: IndexType,
{
    iter: GeneralDfsIndices<'tree, V, Ix>,
}

/// Iterator over node contents and the corresponding node indices in depth-first search order
pub struct GeneralDfs<'tree, V, Ix = DefaultIndexType>
    where
        V: ValueType,
        Ix: IndexType,
{
    iter: GeneralDfsIndices<'tree, V, Ix>,
}

impl<'tree, V, Ix> GeneralDfsIndices<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`
    pub fn new(tree: &'tree dyn Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        let mut v = Vec::new();
        if let Some(rt) = tree.root(node) {
            v.push(rt);
        }
        GeneralDfsIndices {
            tree,
            stack: v,
            size_hint: (0, None),
        }
    }

    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`. The argument `stack_hint` indicates the height of the
    /// `Traversable` tree to be iterated over, such that the internal stack does not need to be
    /// re-allocated.
    pub fn with_capacity(
        tree: &'tree dyn Traversable<V, Ix>,
        node: NodeIndex<Ix>,
        size_hint: usize,
    ) -> Self {
        let mut v = Vec::with_capacity(size_hint);
        if let Some(rt) = tree.root(node) {
            v.push(rt);
        }
        GeneralDfsIndices {
            tree,
            stack: v,
            size_hint: (0, Some(size_hint)),
        }
    }
}

impl<'tree, V, Ix> Iterator for GeneralDfsIndices<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    type Item = NodeIndex<Ix>;

    fn next(&mut self) -> Option<NodeIndex<Ix>> {
        let node = self.stack.pop();
        if let Some(n) = node {
            let cnt = self.tree.child_count(n);
            for pos in (0..cnt).rev() {
                if let Some(c) = self.tree.child(n, pos) {
                    self.stack.push(c);
                }
            }
        }
        node
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.size_hint
    }
}

impl<'tree, V, Ix> GeneralDfsValues<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`
    pub fn new(tree: &'tree dyn Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        GeneralDfsValues {
            iter: GeneralDfsIndices::new(tree, node),
        }
    }

    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`. The argument `stack_hint` indicates the height of the
    /// `Traversable` tree to be iterated over, such that the internal stack does not need to be
    /// re-allocated.
    pub fn with_capacity(
        tree: &'tree dyn Traversable<V, Ix>,
        node: NodeIndex<Ix>,
        size_hint: usize,
    ) -> Self {
        GeneralDfsValues {
            iter: GeneralDfsIndices::with_capacity(tree, node, size_hint),
        }
    }
}

impl<'tree, V, Ix> Iterator for GeneralDfsValues<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    type Item = &'tree V;

    fn next(&mut self) -> Option<&'tree V> {
        self.iter.next().and_then(|n| self.iter.tree.value(n))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'tree, V, Ix> GeneralDfs<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`
    pub fn new(tree: &'tree dyn Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        GeneralDfs {
            iter: GeneralDfsIndices::new(tree, node),
        }
    }

    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`. The argument `stack_hint` indicates the height of the
    /// `Traversable` tree to be iterated over, such that the internal stack does not need to be
    /// re-allocated.
    pub fn with_capacity(
        tree: &'tree dyn Traversable<V, Ix>,
        node: NodeIndex<Ix>,
        size_hint: usize,
    ) -> Self {
        GeneralDfs {
            iter: GeneralDfsIndices::with_capacity(tree, node, size_hint),
        }
    }
}

impl<'tree, V, Ix> Iterator for GeneralDfs<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    type Item = (NodeIndex<Ix>, &'tree V);

    fn next(&mut self) -> Option<(NodeIndex<Ix>, &'tree V)> {
        self.iter
            .next()
            .and_then(|n| self.iter.tree.value(n).map(|v| (n, v)))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// Iterator over node indices in breadth-first search order
pub struct GeneralBfsIndices<'tree, V, Ix = DefaultIndexType>
    where
        V: ValueType,
        Ix: IndexType,
{
    tree: &'tree dyn Traversable<V, Ix>,
    queue: VecDeque<NodeIndex<Ix>>,
    size_hint: (usize, Option<usize>),
}

/// Iterator over node contents in breadth-first search order
pub struct GeneralBfsValues<'tree, V, Ix = DefaultIndexType>
    where
        V: ValueType,
        Ix: IndexType,
{
    iter: GeneralBfsIndices<'tree, V, Ix>,
}

/// Iterator over node contents and the corresponding node indices in breadth-first search order
pub struct GeneralBfs<'tree, V, Ix = DefaultIndexType>
    where
        V: ValueType,
        Ix: IndexType,
{
    iter: GeneralBfsIndices<'tree, V, Ix>,
}

impl<'tree, V, Ix> GeneralBfsIndices<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`
    pub fn new(tree: &'tree dyn Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        let mut v = VecDeque::new();
        if let Some(rt) = tree.root(node) {
            v.push_front(rt);
        }
        GeneralBfsIndices {
            tree,
            queue: v,
            size_hint: (0, None),
        }
    }

    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`. The argument `stack_hint` indicates the height of the
    /// `Traversable` tree to be iterated over, such that the internal stack does not need to be
    /// re-allocated.
    pub fn with_capacity(
        tree: &'tree dyn Traversable<V, Ix>,
        node: NodeIndex<Ix>,
        size_hint: usize,
    ) -> Self {
        let mut v = VecDeque::with_capacity(size_hint);
        if let Some(rt) = tree.root(node) {
            v.push_front(rt);
        }
        GeneralBfsIndices {
            tree,
            queue: v,
            size_hint: (0, Some(size_hint)),
        }
    }
}

impl<'tree, V, Ix> Iterator for GeneralBfsIndices<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    type Item = NodeIndex<Ix>;

    fn next(&mut self) -> Option<NodeIndex<Ix>> {
        let node = self.queue.pop_front();
        if let Some(n) = node {
            let cnt = self.tree.child_count(n);
            for pos in 0..cnt {
                if let Some(c) = self.tree.child(n, pos) {
                    self.queue.push_back(c);
                }
            }
        }
        node
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.size_hint
    }
}

impl<'tree, V, Ix> GeneralBfsValues<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`
    pub fn new(tree: &'tree dyn Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        GeneralBfsValues {
            iter: GeneralBfsIndices::new(tree, node),
        }
    }

    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`. The argument `stack_hint` indicates the height of the
    /// `Traversable` tree to be iterated over, such that the internal stack does not need to be
    /// re-allocated.
    pub fn with_capacity(
        tree: &'tree dyn Traversable<V, Ix>,
        node: NodeIndex<Ix>,
        size_hint: usize,
    ) -> Self {
        GeneralBfsValues {
            iter: GeneralBfsIndices::with_capacity(tree, node, size_hint),
        }
    }
}

impl<'tree, V, Ix> Iterator for GeneralBfsValues<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    type Item = &'tree V;

    fn next(&mut self) -> Option<&'tree V> {
        self.iter.next().and_then(|n| self.iter.tree.value(n))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'tree, V, Ix> GeneralBfs<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`
    pub fn new(tree: &'tree dyn Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        GeneralBfs {
            iter: GeneralBfsIndices::new(tree, node),
        }
    }

    /// Construct an iterator over **all** nodes of the `Traversable` tree containing
    /// the tree node indexed by `node`. The argument `stack_hint` indicates the height of the
    /// `Traversable` tree to be iterated over, such that the internal stack does not need to be
    /// re-allocated.
    pub fn with_capacity(
        tree: &'tree dyn Traversable<V, Ix>,
        node: NodeIndex<Ix>,
        size_hint: usize,
    ) -> Self {
        GeneralBfs {
            iter: GeneralBfsIndices::with_capacity(tree, node, size_hint),
        }
    }
}

impl<'tree, V, Ix> Iterator for GeneralBfs<'tree, V, Ix>
    where
        V: ValueType,
        Ix: IndexType,
{
    type Item = (NodeIndex<Ix>, &'tree V);

    fn next(&mut self) -> Option<(NodeIndex<Ix>, &'tree V)> {
        self.iter
            .next()
            .and_then(|n| self.iter.tree.value(n).map(|v| (n, v)))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}
