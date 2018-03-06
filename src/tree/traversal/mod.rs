use std::collections::VecDeque;
use types::{DefaultIndexType, IndexType, NodeIndex, ValueType};

#[cfg(test)]
mod tests;

pub trait Traversable<V, Ix = DefaultIndexType>
where
    V: ValueType,
    Ix: IndexType,
{
    fn root(&self, node: NodeIndex<Ix>) -> Option<NodeIndex<Ix>>;
    fn value(&self, node: NodeIndex<Ix>) -> Option<&V>;
    fn value_mut(&mut self, node: NodeIndex<Ix>) -> Option<&mut V>;
    fn parent(&self, node: NodeIndex<Ix>) -> Option<NodeIndex<Ix>>;
    fn child(&self, node: NodeIndex<Ix>, pos: usize) -> Option<NodeIndex<Ix>>;
    fn child_count(&self, node: NodeIndex<Ix>) -> usize;
    fn node_count(&self) -> usize;
}

pub struct BinaryInOrderIndices<'tree, V, Ix = DefaultIndexType>
where
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    tree: &'tree Traversable<V, Ix>,
    current: Option<NodeIndex<Ix>>,
    stack: Vec<NodeIndex<Ix>>,
    size_hint: (usize, Option<usize>),
}

pub struct BinaryInOrderValues<'tree, V, Ix = DefaultIndexType>
where
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    iter: BinaryInOrderIndices<'tree, V, Ix>,
}

pub struct BinaryInOrder<'tree, V, Ix = DefaultIndexType>
where
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    iter: BinaryInOrderIndices<'tree, V, Ix>,
}

impl<'tree, V, Ix> BinaryInOrderIndices<'tree, V, Ix>
where
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    pub fn new(tree: &'tree Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        let rt = tree.root(node);
        BinaryInOrderIndices {
            tree: tree,
            current: rt,
            stack: Vec::new(),
            size_hint: (0, None),
        }
    }

    pub fn with_capacity(
        tree: &'tree Traversable<V, Ix>,
        node: NodeIndex<Ix>,
        size_hint: usize,
    ) -> Self {
        let rt = tree.root(node);
        let stack_hint = (size_hint as f64).log2().floor() as usize;
        BinaryInOrderIndices {
            tree: tree,
            current: rt,
            stack: Vec::with_capacity(stack_hint),
            size_hint: (0, Some(size_hint)),
        }
    }
}

impl<'tree, V, Ix> Iterator for BinaryInOrderIndices<'tree, V, Ix>
where
    V: 'tree + ValueType,
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
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    pub fn new(tree: &'tree Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        BinaryInOrderValues {
            iter: BinaryInOrderIndices::new(tree, node),
        }
    }

    pub fn with_capacity(
        tree: &'tree Traversable<V, Ix>,
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
    V: 'tree + ValueType,
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
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    pub fn new(tree: &'tree Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        BinaryInOrder {
            iter: BinaryInOrderIndices::new(tree, node),
        }
    }

    pub fn with_capacity(
        tree: &'tree Traversable<V, Ix>,
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
    V: 'tree + ValueType,
    Ix: IndexType,
{
    type Item = (NodeIndex<Ix>, &'tree V);

    fn next(&mut self) -> Option<(NodeIndex<Ix>, &'tree V)> {
        self.iter
            .next()
            .and_then(|n| self.iter.tree.value(n).and_then(|v| Some((n, v))))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

pub struct BinaryPreOrderIndices<'tree, V, Ix = DefaultIndexType>
where
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    tree: &'tree Traversable<V, Ix>,
    stack: Vec<NodeIndex<Ix>>,
    size_hint: (usize, Option<usize>),
}

pub struct BinaryPreOrderValues<'tree, V, Ix = DefaultIndexType>
where
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    iter: BinaryPreOrderIndices<'tree, V, Ix>,
}

pub struct BinaryPreOrder<'tree, V, Ix = DefaultIndexType>
where
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    iter: BinaryPreOrderIndices<'tree, V, Ix>,
}

impl<'tree, V, Ix> BinaryPreOrderIndices<'tree, V, Ix>
where
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    pub fn new(tree: &'tree Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        let mut v = Vec::new();
        tree.root(node).map(|rt| v.push(rt));
        BinaryPreOrderIndices {
            tree: tree,
            stack: v,
            size_hint: (0, None),
        }
    }

    pub fn with_capacity(
        tree: &'tree Traversable<V, Ix>,
        node: NodeIndex<Ix>,
        size_hint: usize,
    ) -> Self {
        let stack_hint = (size_hint as f64).log2().floor() as usize;
        let mut v = Vec::with_capacity(stack_hint);
        tree.root(node).map(|rt| v.push(rt));
        BinaryPreOrderIndices {
            tree: tree,
            stack: v,
            size_hint: (0, Some(size_hint)),
        }
    }
}

impl<'tree, V, Ix> Iterator for BinaryPreOrderIndices<'tree, V, Ix>
where
    V: 'tree + ValueType,
    Ix: IndexType,
{
    type Item = NodeIndex<Ix>;

    fn next(&mut self) -> Option<NodeIndex<Ix>> {
        let node = self.stack.pop();
        node.map(|n| {
            self.tree.child(n, 1).map(|c| self.stack.push(c));
            self.tree.child(n, 0).map(|c| self.stack.push(c));
        });
        node
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.size_hint
    }
}

impl<'tree, V, Ix> BinaryPreOrderValues<'tree, V, Ix>
where
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    pub fn new(tree: &'tree Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        BinaryPreOrderValues {
            iter: BinaryPreOrderIndices::new(tree, node),
        }
    }

    pub fn with_capacity(
        tree: &'tree Traversable<V, Ix>,
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
    V: 'tree + ValueType,
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
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    pub fn new(tree: &'tree Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        BinaryPreOrder {
            iter: BinaryPreOrderIndices::new(tree, node),
        }
    }

    pub fn with_capacity(
        tree: &'tree Traversable<V, Ix>,
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
    V: 'tree + ValueType,
    Ix: IndexType,
{
    type Item = (NodeIndex<Ix>, &'tree V);

    fn next(&mut self) -> Option<(NodeIndex<Ix>, &'tree V)> {
        self.iter
            .next()
            .and_then(|n| self.iter.tree.value(n).and_then(|v| Some((n, v))))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

pub struct BinaryPostOrderIndices<'tree, V, Ix = DefaultIndexType>
where
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    tree: &'tree Traversable<V, Ix>,
    current: Option<NodeIndex<Ix>>,
    stack: Vec<NodeIndex<Ix>>,
    size_hint: (usize, Option<usize>),
}

pub struct BinaryPostOrderValues<'tree, V, Ix = DefaultIndexType>
where
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    iter: BinaryPostOrderIndices<'tree, V, Ix>,
}

pub struct BinaryPostOrder<'tree, V, Ix = DefaultIndexType>
where
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    iter: BinaryPostOrderIndices<'tree, V, Ix>,
}

impl<'tree, V, Ix> BinaryPostOrderIndices<'tree, V, Ix>
where
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    pub fn new(tree: &'tree Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        let rt = tree.root(node);
        BinaryPostOrderIndices {
            tree: tree,
            current: rt,
            stack: Vec::new(),
            size_hint: (0, None),
        }
    }

    pub fn with_capacity(
        tree: &'tree Traversable<V, Ix>,
        node: NodeIndex<Ix>,
        size_hint: usize,
    ) -> Self {
        let rt = tree.root(node);
        let stack_hint = (size_hint as f64).log2().floor() as usize;
        BinaryPostOrderIndices {
            tree: tree,
            current: rt,
            stack: Vec::with_capacity(stack_hint),
            size_hint: (0, Some(size_hint)),
        }
    }
}

impl<'tree, V, Ix> Iterator for BinaryPostOrderIndices<'tree, V, Ix>
where
    V: 'tree + ValueType,
    Ix: IndexType,
{
    type Item = NodeIndex<Ix>;

    fn next(&mut self) -> Option<NodeIndex<Ix>> {
        loop {
            if let Some(n) = self.current {
                self.tree.child(n, 1).map(|c| self.stack.push(c));
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
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    pub fn new(tree: &'tree Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        BinaryPostOrderValues {
            iter: BinaryPostOrderIndices::new(tree, node),
        }
    }

    pub fn with_capacity(
        tree: &'tree Traversable<V, Ix>,
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
    V: 'tree + ValueType,
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
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    pub fn new(tree: &'tree Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        BinaryPostOrder {
            iter: BinaryPostOrderIndices::new(tree, node),
        }
    }

    pub fn with_capacity(
        tree: &'tree Traversable<V, Ix>,
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
    V: 'tree + ValueType,
    Ix: IndexType,
{
    type Item = (NodeIndex<Ix>, &'tree V);

    fn next(&mut self) -> Option<(NodeIndex<Ix>, &'tree V)> {
        self.iter
            .next()
            .and_then(|n| self.iter.tree.value(n).and_then(|v| Some((n, v))))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

pub struct GeneralDfsIndices<'tree, V, Ix = DefaultIndexType>
where
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    tree: &'tree Traversable<V, Ix>,
    stack: Vec<NodeIndex<Ix>>,
    size_hint: (usize, Option<usize>),
}

pub struct GeneralDfsValues<'tree, V, Ix = DefaultIndexType>
where
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    iter: GeneralDfsIndices<'tree, V, Ix>,
}

pub struct GeneralDfs<'tree, V, Ix = DefaultIndexType>
where
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    iter: GeneralDfsIndices<'tree, V, Ix>,
}

impl<'tree, V, Ix> GeneralDfsIndices<'tree, V, Ix>
where
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    pub fn new(tree: &'tree Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        let mut v = Vec::new();
        tree.root(node).map(|rt| v.push(rt));
        GeneralDfsIndices {
            tree: tree,
            stack: v,
            size_hint: (0, None),
        }
    }

    pub fn with_capacity(
        tree: &'tree Traversable<V, Ix>,
        node: NodeIndex<Ix>,
        size_hint: usize,
    ) -> Self {
        let mut v = Vec::with_capacity(size_hint);
        tree.root(node).map(|rt| v.push(rt));
        GeneralDfsIndices {
            tree: tree,
            stack: v,
            size_hint: (0, Some(size_hint)),
        }
    }
}

impl<'tree, V, Ix> Iterator for GeneralDfsIndices<'tree, V, Ix>
where
    V: 'tree + ValueType,
    Ix: IndexType,
{
    type Item = NodeIndex<Ix>;

    fn next(&mut self) -> Option<NodeIndex<Ix>> {
        let node = self.stack.pop();
        if let Some(n) = node {
            let cnt = self.tree.child_count(n);
            for pos in (0..cnt).rev() {
                self.tree.child(n, pos).map(|c| self.stack.push(c));
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
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    pub fn new(tree: &'tree Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        GeneralDfsValues {
            iter: GeneralDfsIndices::new(tree, node),
        }
    }

    pub fn with_capacity(
        tree: &'tree Traversable<V, Ix>,
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
    V: 'tree + ValueType,
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
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    pub fn new(tree: &'tree Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        GeneralDfs {
            iter: GeneralDfsIndices::new(tree, node),
        }
    }

    pub fn with_capacity(
        tree: &'tree Traversable<V, Ix>,
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
    V: 'tree + ValueType,
    Ix: IndexType,
{
    type Item = (NodeIndex<Ix>, &'tree V);

    fn next(&mut self) -> Option<(NodeIndex<Ix>, &'tree V)> {
        self.iter
            .next()
            .and_then(|n| self.iter.tree.value(n).and_then(|v| Some((n, v))))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

pub struct GeneralBfsIndices<'tree, V, Ix = DefaultIndexType>
where
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    tree: &'tree Traversable<V, Ix>,
    queue: VecDeque<NodeIndex<Ix>>,
    size_hint: (usize, Option<usize>),
}

pub struct GeneralBfsValues<'tree, V, Ix = DefaultIndexType>
where
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    iter: GeneralBfsIndices<'tree, V, Ix>,
}

pub struct GeneralBfs<'tree, V, Ix = DefaultIndexType>
where
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    iter: GeneralBfsIndices<'tree, V, Ix>,
}

impl<'tree, V, Ix> GeneralBfsIndices<'tree, V, Ix>
where
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    pub fn new(tree: &'tree Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        let mut v = VecDeque::new();
        tree.root(node).map(|rt| v.push_front(rt));
        GeneralBfsIndices {
            tree: tree,
            queue: v,
            size_hint: (0, None),
        }
    }

    pub fn with_capacity(
        tree: &'tree Traversable<V, Ix>,
        node: NodeIndex<Ix>,
        size_hint: usize,
    ) -> Self {
        let mut v = VecDeque::with_capacity(size_hint);
        tree.root(node).map(|rt| v.push_front(rt));
        GeneralBfsIndices {
            tree: tree,
            queue: v,
            size_hint: (0, Some(size_hint)),
        }
    }
}

impl<'tree, V, Ix> Iterator for GeneralBfsIndices<'tree, V, Ix>
where
    V: 'tree + ValueType,
    Ix: IndexType,
{
    type Item = NodeIndex<Ix>;

    fn next(&mut self) -> Option<NodeIndex<Ix>> {
        let node = self.queue.pop_front();
        if let Some(n) = node {
            let cnt = self.tree.child_count(n);
            for pos in 0..cnt {
                self.tree.child(n, pos).map(|c| self.queue.push_back(c));
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
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    pub fn new(tree: &'tree Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        GeneralBfsValues {
            iter: GeneralBfsIndices::new(tree, node),
        }
    }

    pub fn with_capacity(
        tree: &'tree Traversable<V, Ix>,
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
    V: 'tree + ValueType,
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
    V: 'tree + ValueType,
    Ix: 'tree + IndexType,
{
    pub fn new(tree: &'tree Traversable<V, Ix>, node: NodeIndex<Ix>) -> Self {
        GeneralBfs {
            iter: GeneralBfsIndices::new(tree, node),
        }
    }

    pub fn with_capacity(
        tree: &'tree Traversable<V, Ix>,
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
    V: 'tree + ValueType,
    Ix: IndexType,
{
    type Item = (NodeIndex<Ix>, &'tree V);

    fn next(&mut self) -> Option<(NodeIndex<Ix>, &'tree V)> {
        self.iter
            .next()
            .and_then(|n| self.iter.tree.value(n).and_then(|v| Some((n, v))))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}
