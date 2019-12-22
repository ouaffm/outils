//!
//! `DynamicGraph<W>` is graph data structure providing fully-dynamic connectivity with support
//! for vertex and component weights.
//!
use crate::graph::dynconn::{DynamicComponent, DynamicConnectivity, DynamicWeightedComponent};
use slab::Slab;
use std::marker::PhantomData;
use std::mem::{size_of, swap};
use std::ops::{Add, AddAssign};
use std::ops::{Index, IndexMut};
use crate::tree::bst::{BalancedBinaryForest, BstDirection, OrderedTree};
use crate::tree::bst::waaforest::WeightedAaForest;
use crate::tree::traversal::Traversable;
use crate::tree::WeightedTree;
use crate::types::{Edge, EdgeIndex, Edges, EmptyWeight, NodeIndex, Values, VertexIndex, WeightType};

#[cfg(test)]
mod tests;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum EdgeDirection {
    Incoming = 0,
    Outgoing = 1,
}

type BalancedForest<W> = WeightedAaForest<EulerVertex, VertexWeight<W>>;

#[derive(Debug, Default, Copy, Clone, Eq, PartialEq, PartialOrd, Ord, Hash)]
struct VertexWeight<W>
where
    W: WeightType,
{
    adj_count: usize,
    act_count: usize,
    weight: W,
}

impl<W> VertexWeight<W>
where
    W: WeightType,
{
    fn new(adj_count: usize, act_count: usize) -> Self {
        VertexWeight {
            adj_count,
            act_count,
            weight: W::default(),
        }
    }
}

impl<W> Add for VertexWeight<W>
where
    W: WeightType,
{
    type Output = VertexWeight<W>;

    fn add(self, other: VertexWeight<W>) -> VertexWeight<W> {
        VertexWeight {
            adj_count: self.adj_count + other.adj_count,
            act_count: self.act_count + other.act_count,
            weight: self.weight + other.weight,
        }
    }
}

impl<W> AddAssign for VertexWeight<W>
where
    W: WeightType,
{
    fn add_assign(&mut self, other: VertexWeight<W>) {
        *self = VertexWeight {
            adj_count: self.adj_count + other.adj_count,
            act_count: self.act_count + other.act_count,
            weight: self.weight + other.weight,
        }
    }
}

#[derive(Clone, Debug)]
struct DynamicVertex {
    active_node: NodeIndex,
    tree_edges: Slab<EulerHalfEdge>,
    adj_edges: Vec<EdgeIndex>,
}

impl DynamicVertex {
    fn new(adjacency_hint: usize) -> Self {
        DynamicVertex {
            active_node: NodeIndex::default(),
            tree_edges: Slab::with_capacity(adjacency_hint),
            adj_edges: Vec::with_capacity(adjacency_hint),
        }
    }
}

#[derive(Clone, Debug)]
struct DynamicVertexList {
    vertices: Vec<DynamicVertex>,
}

impl DynamicVertexList {
    fn new(size: usize) -> Self {
        DynamicVertexList {
            vertices: Vec::with_capacity(size),
        }
    }

    fn insert(&mut self, v: DynamicVertex) -> VertexIndex {
        let idx = self.vertices.len();
        self.vertices.push(v);
        VertexIndex(idx)
    }
}

impl Index<VertexIndex> for DynamicVertexList {
    type Output = DynamicVertex;
    fn index(&self, index: VertexIndex) -> &Self::Output {
        &self.vertices[index.index()]
    }
}

impl IndexMut<VertexIndex> for DynamicVertexList {
    fn index_mut(&mut self, index: VertexIndex) -> &mut DynamicVertex {
        &mut self.vertices[index.index()]
    }
}

#[derive(Copy, Clone, Debug, Default)]
struct DynamicEdge {
    level: usize,
    is_tree_edge: bool,
    src: VertexIndex,
    dst: VertexIndex,
}

impl DynamicEdge {
    fn new(src: VertexIndex, dst: VertexIndex) -> Self {
        DynamicEdge {
            level: 0,
            is_tree_edge: false,
            src,
            dst,
        }
    }
}

#[derive(Clone, Debug)]
struct DynamicEdgeList {
    edges: Slab<DynamicEdge>,
}

impl DynamicEdgeList {
    fn new(size: usize) -> Self {
        DynamicEdgeList {
            edges: Slab::with_capacity(size),
        }
    }

    fn insert(&mut self, e: DynamicEdge) -> EdgeIndex {
        EdgeIndex(self.edges.insert(e))
    }

    fn remove(&mut self, e: EdgeIndex) -> DynamicEdge {
        self.edges.remove(e.index())
    }
}

impl Index<EdgeIndex> for DynamicEdgeList {
    type Output = DynamicEdge;
    fn index(&self, index: EdgeIndex) -> &Self::Output {
        &self.edges[index.index()]
    }
}

impl IndexMut<EdgeIndex> for DynamicEdgeList {
    fn index_mut(&mut self, index: EdgeIndex) -> &mut DynamicEdge {
        &mut self.edges[index.index()]
    }
}

impl Index<Edge> for DynamicEdgeList {
    type Output = DynamicEdge;
    fn index(&self, index: Edge) -> &Self::Output {
        &self.edges[index.index().index()]
    }
}

impl IndexMut<Edge> for DynamicEdgeList {
    fn index_mut(&mut self, index: Edge) -> &mut DynamicEdge {
        &mut self.edges[index.index().index()]
    }
}

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, Hash)]
struct EulerVertex {
    vertex: VertexIndex,
    half_edge_index: [Option<usize>; 2],
}

impl EulerVertex {
    fn new(vertex: VertexIndex) -> Self {
        EulerVertex {
            vertex,
            half_edge_index: [None, None],
        }
    }
}

impl Index<EdgeDirection> for EulerVertex {
    type Output = Option<usize>;
    fn index(&self, index: EdgeDirection) -> &Option<usize> {
        &self.half_edge_index[index as usize]
    }
}

impl IndexMut<EdgeDirection> for EulerVertex {
    fn index_mut(&mut self, index: EdgeDirection) -> &mut Option<usize> {
        &mut self.half_edge_index[index as usize]
    }
}

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
struct EulerHalfEdge {
    edge: EdgeIndex,
    nodes: [NodeIndex; 2],
}

impl EulerHalfEdge {
    fn new(edge: EdgeIndex, incoming: NodeIndex, outgoing: NodeIndex) -> Self {
        EulerHalfEdge {
            edge,
            nodes: [incoming, outgoing],
        }
    }
}

impl Index<EdgeDirection> for EulerHalfEdge {
    type Output = NodeIndex;
    fn index(&self, index: EdgeDirection) -> &NodeIndex {
        &self.nodes[index as usize]
    }
}

impl IndexMut<EdgeDirection> for EulerHalfEdge {
    fn index_mut(&mut self, index: EdgeDirection) -> &mut NodeIndex {
        &mut self.nodes[index as usize]
    }
}

struct EulerCutContext {
    v: VertexIndex,
    hv_idx: usize,
    v1: NodeIndex,
    v2: NodeIndex,
    w: VertexIndex,
    hw_idx: usize,
    w1: NodeIndex,
    w2: NodeIndex,
}

#[derive(Clone, Debug)]
struct EulerForest<W>
where
    W: WeightType,
{
    forest: BalancedForest<W>,
    vertices: DynamicVertexList,
}

impl<W> EulerForest<W>
where
    W: WeightType,
{
    fn new(size: usize, adjacency_hint: usize) -> Self {
        let mut vertices = DynamicVertexList::new(size);
        let mut forest = if size > 0 {
            BalancedForest::new((size * 2) - 1)
        } else {
            BalancedForest::new(0)
        };
        for _ in 0..size {
            let v = vertices.insert(DynamicVertex::new(adjacency_hint));
            let n = forest.insert(EulerVertex::new(v));
            forest.set_weight(n, VertexWeight::new(0, 1));
            vertices[v].active_node = n;
        }
        EulerForest { vertices, forest }
    }

    fn create_vertex(&mut self, v: EulerVertex) -> NodeIndex {
        let v1 = self.forest.insert(v);
        self.forest.set_weight(v1, VertexWeight::default());
        v1
    }

    fn pass_activity(&mut self, v: NodeIndex, w: NodeIndex) {
        let weight_v = self
            .forest
            .weight(v)
            .map_or(VertexWeight::default(), |wv| *wv);
        if weight_v.act_count == 0 {
            return;
        }
        self.forest.set_weight(w, weight_v);
        let value_v = self.forest[v];
        self.vertices[value_v.vertex].active_node = w;
    }

    fn find_half_edge(&self, v: VertexIndex, e: EdgeIndex) -> Option<usize> {
        for (i, h) in self.vertices[v].tree_edges.iter() {
            if h.edge == e {
                return Some(i);
            }
        }
        None
    }

    fn insert_adjacent_edge(&mut self, v: VertexIndex, e: EdgeIndex) {
        self.vertices[v].adj_edges.push(e);
        let n = self.vertices[v].active_node;
        self.forest
            .adjust_weight(n, &|w: &mut VertexWeight<W>| (*w).adj_count += 1);
    }

    fn delete_adjacent_edge(&mut self, v: VertexIndex, idx: usize) {
        let v_act = self.vertices[v].active_node;
        self.vertices[v].adj_edges.remove(idx);
        self.forest
            .adjust_weight(v_act, &|w: &mut VertexWeight<W>| (*w).adj_count -= 1);
    }

    fn adjacent_edge_index(&self, v: VertexIndex, e: EdgeIndex) -> Option<usize> {
        let adj = &self.vertices[v].adj_edges;
        for (i, edge) in adj.iter().enumerate() {
            if *edge == e {
                return Some(i);
            }
        }
        None
    }

    fn tree_roots_ordered(&self, src: VertexIndex, dst: VertexIndex) -> (NodeIndex, NodeIndex) {
        let (left, right) = self.tree_roots(src, dst);
        let left_tree_weight = self
            .forest
            .subweight(left)
            .map_or(VertexWeight::default(), |w| *w);
        let right_tree_weight = self
            .forest
            .subweight(right)
            .map_or(VertexWeight::default(), |w| *w);
        if right_tree_weight.act_count < left_tree_weight.act_count {
            return (right, left);
        }
        (left, right)
    }

    fn tree_roots(&self, src: VertexIndex, dst: VertexIndex) -> (NodeIndex, NodeIndex) {
        let src_occ = self.vertices[src].active_node;
        let dst_occ = self.vertices[dst].active_node;
        let src_tree = self
            .forest
            .root(src_occ)
            .expect("trees(): root(src_occ) should never return None");
        let dst_tree = self
            .forest
            .root(dst_occ)
            .expect("trees(): root(dst_occ) should never return None");
        (src_tree, dst_tree)
    }

    fn make_first(&mut self, v1: NodeIndex) {
        let root = self
            .forest
            .root(v1)
            .expect("make_first(): root() should never return None");

        let w1 = self
            .forest
            .first(root)
            .expect("make_first(): first() should never return None");

        if v1 == w1 {
            return;
        }

        let v = self.forest[v1].vertex;
        let w = self.forest[w1].vertex;
        let hv_inc_idx = self.forest[v1][EdgeDirection::Incoming]
            .expect("make_first(): incoming half edge of new first should never be None");
        let hw_out_idx = self.forest[w1][EdgeDirection::Outgoing]
            .expect("make_first(): outgoing half edge of current first should never be None");

        let w2 = self
            .forest
            .last(root)
            .expect("make_first(): last() should never return None");
        let value_v1 = self.forest[v1];
        let v2 = self.create_vertex(value_v1);

        self.pass_activity(w1, w2);

        self.forest[v1][EdgeDirection::Incoming] = None;
        self.forest[v2][EdgeDirection::Incoming] = Some(hv_inc_idx);
        self.forest[v2][EdgeDirection::Outgoing] = None;
        self.forest[w2][EdgeDirection::Outgoing] = Some(hw_out_idx);

        self.vertices[v].tree_edges[hv_inc_idx][EdgeDirection::Incoming] = v2;
        self.vertices[w].tree_edges[hw_out_idx][EdgeDirection::Outgoing] = w2;

        self.forest.remove(w1);

        match self.forest.split(v1, BstDirection::Right) {
            (Some(mut prefix), Some(postfix)) => {
                prefix = self
                    .forest
                    .append(prefix, v2)
                    .expect("make_first(): append() should never return None");
                self.forest
                    .append(postfix, prefix)
                    .expect("make_first(): append() should never return None");
            }
            (Some(prefix), None) => {
                self.forest
                    .append(prefix, v2)
                    .expect("make_first(): append() should never return None");
            }
            (None, Some(postfix)) => {
                self.forest
                    .append(postfix, v2)
                    .expect("make_first(): append() should never return None");
            }
            (None, None) => {
                panic!("make_first(): split() should never return (None, None");
            }
        }
    }

    fn link(&mut self, e1: EdgeIndex, edges: &DynamicEdgeList) {
        let v = edges[e1].src;
        let w = edges[e1].dst;
        let v1 = self.vertices[v].active_node;
        let w1 = self.vertices[w].active_node;

        let v2 = self.create_vertex(EulerVertex::new(v));

        self.make_first(w1);
        let w_root = self
            .forest
            .root(w1)
            .expect("link(): root() should never return None");
        let w2 = self
            .forest
            .last(w_root)
            .expect("link(): last() should never return None");

        let hv = self.vertices[v]
            .tree_edges
            .insert(EulerHalfEdge::new(e1, v2, v1));

        let hw = self.vertices[w]
            .tree_edges
            .insert(EulerHalfEdge::new(e1, w1, w2));

        let hv_out_idx = self.forest[v1][EdgeDirection::Outgoing];

        let infix = self
            .forest
            .append(w1, v2)
            .expect("link(): append() should never return None");

        match self.forest.split(v1, BstDirection::Left) {
            (Some(mut prefix), Some(postfix)) => {
                prefix = self
                    .forest
                    .append(prefix, infix)
                    .expect("link(): append() should never return None");
                self.forest
                    .append(prefix, postfix)
                    .expect("link(): append() should never return None");
            }
            (Some(prefix), None) => {
                self.forest
                    .append(prefix, infix)
                    .expect("link(): append() should never return None");
            }
            (None, Some(postfix)) => {
                self.forest
                    .append(infix, postfix)
                    .expect("link(): append() should never return None");
            }
            (None, None) => {
                panic!("make_first(): split() should never return (None, None");
            }
        }

        self.forest[v1][EdgeDirection::Outgoing] = Some(hv);
        self.forest[v2][EdgeDirection::Incoming] = Some(hv);
        self.forest[v2][EdgeDirection::Outgoing] = hv_out_idx;
        self.forest[w1][EdgeDirection::Incoming] = Some(hw);
        self.forest[w2][EdgeDirection::Outgoing] = Some(hw);

        if let Some(i) = hv_out_idx {
            self.vertices[v].tree_edges[i][EdgeDirection::Outgoing] = v2
        }
    }

    fn cut_context(&self, e: EdgeIndex, edges: &DynamicEdgeList) -> EulerCutContext {
        let s = edges[e].src;
        let hs_idx = self
            .find_half_edge(s, e)
            .expect("cut_context(): find_half_edge() should never return None");
        let mut s1 = self.vertices[s].tree_edges[hs_idx][EdgeDirection::Outgoing];
        let mut s2 = self.vertices[s].tree_edges[hs_idx][EdgeDirection::Incoming];
        let d = edges[e].dst;
        let hd_idx = self
            .find_half_edge(d, e)
            .expect("cut_context(): find_half_edge() should never return None");
        let mut d1 = self.vertices[d].tree_edges[hd_idx][EdgeDirection::Outgoing];
        let mut d2 = self.vertices[d].tree_edges[hd_idx][EdgeDirection::Incoming];

        if self.forest.is_smaller(s2, s1) {
            swap(&mut s1, &mut s2);
        }
        if self.forest.is_smaller(d2, d1) {
            swap(&mut d1, &mut d2);
        }

        if self.forest.is_smaller(d1, s1) {
            EulerCutContext {
                v: d,
                hv_idx: hd_idx,
                v1: d1,
                v2: d2,
                w: s,
                hw_idx: hs_idx,
                w1: s1,
                w2: s2,
            }
        } else {
            EulerCutContext {
                v: s,
                hv_idx: hs_idx,
                v1: s1,
                v2: s2,
                w: d,
                hw_idx: hd_idx,
                w1: d1,
                w2: d2,
            }
        }
    }

    fn cut(&mut self, e1: EdgeIndex, edges: &DynamicEdgeList) {
        let ctx = self.cut_context(e1, edges);
        let hv_e2_idx = self.forest[ctx.v2][EdgeDirection::Outgoing];

        let prefix = self
            .forest
            .split(ctx.v1, BstDirection::Left)
            .0
            .expect("cut(): split() should never return None");
        let postfix = self
            .forest
            .split(ctx.v2, BstDirection::Right)
            .1
            .expect("cut(): split() should never return None");

        self.forest.append(prefix, postfix);
        self.pass_activity(ctx.v2, ctx.v1);
        self.forest.remove(ctx.v2);

        self.forest[ctx.w1][EdgeDirection::Incoming] = None;
        self.forest[ctx.w2][EdgeDirection::Outgoing] = None;

        self.forest[ctx.v1][EdgeDirection::Outgoing] = hv_e2_idx;

        if let Some(i) = hv_e2_idx {
            self.vertices[ctx.v].tree_edges[i][EdgeDirection::Outgoing] = ctx.v1;
        }

        self.vertices[ctx.v].tree_edges.remove(ctx.hv_idx);
        self.vertices[ctx.w].tree_edges.remove(ctx.hw_idx);
    }

    fn is_connected(&self, v: VertexIndex, w: VertexIndex) -> bool {
        let act_v = self.vertices[v].active_node;
        let act_w = self.vertices[w].active_node;
        let root_v = self.forest.root(act_v);
        let root_w = self.forest.root(act_w);
        root_v
            .and_then(|v| root_w.map(|w| v == w))
            .map_or(false, |r| r)
    }
}

/// `DynamicGraph<W>` is general graph data structure providing deterministic fully-dynamic
/// connectivity for a graph with a fixed set of vertices.
///
/// That is, operations are provided to answer queries as to whether two vertices are
/// connected in a graph through a path of edges. In this context, _fully dynamic_ means that the
/// graph can be updated by insertions or deletions of edges through the provided operations
/// between queries (see also [Dynamic Connectivity][1]).
///
/// The data structure also supports vertex weights of type `W`, dynamically maintaining the
/// total weight of connected components after insertion or deletion of edges.
///
/// The principal operations for a graph `G = (V, E)` with `|V| = n` have a poly-logarithmic
/// run-time cost:
///
/// - [`insert_edge`](#method.insert_edge): O(log^2 (n))
/// - [`delete_edge`](#method.delete_edge): O(log^2 (n))
/// - [`is_connected`](#method.insert_connected): O(log(n))
///
/// The space requirement of the data structure is O(log(n) * n).
///
/// This is achieved by maintaining the [spanning forest][2] of the graph under insertions and
/// deletions of edges. The complexity in maintaining a spanning forest lies in the fact that the
/// deletion of an edge might split a tree in the spanning forest into two trees but not disconnect
/// the connected component. In this situation, the algorithm must try to reconnect the trees by
/// finding a replacement edge - the component is only accepted to have been disconnected by the
/// edge deletion if no replacement edge has been found.
///
/// In order to efficiently search for replacement edges, this data structure utilises the
/// [level structure][3], trading-off time for memory. The implemented version is outlined by
/// Holm, de Lichtenberg and Thorup in [Poly-Logarithmic Deterministic Fully-Dynamic Algorithms][4].
///
/// **Note:** The above-mentioned trade-off of time against memory does not affect the storage of
/// vertex weights. Vertex and component weights are not managed within the level structure, and
/// therefore have a constant additional space requirement of O(n).
///
/// The usage of `DynamicGraph<W>` is straight-forward:
///
/// ```
/// use outils::prelude::*;
///
/// // Construct a unweighted dynamic graph with a fixed number of 10 vertices with an expected
/// // degree (i.e. number of adjacent edges) of 3.
/// let mut graph: DynamicGraph<EmptyWeight> = DynamicGraph::new(10, 3);
///
/// let a = VertexIndex(0);
/// let b = VertexIndex(1);
/// let c = VertexIndex(2);
/// let d = VertexIndex(3);
///
/// // Create a cycle from a to d.
/// let ab = graph.insert_edge(a, b).expect("No reason to fail here");
/// let bc = graph.insert_edge(b, c).expect("No reason to fail here");
/// let cd = graph.insert_edge(c, d).expect("No reason to fail here");
/// let da = graph.insert_edge(d, a).expect("No reason to fail here");
///
/// // a and c should be connected:
/// assert!(graph.is_connected(a, c));
///
/// graph.delete_edge(bc);
///
/// // a and c should still be connected:
/// assert!(graph.is_connected(a, c));
///
/// graph.delete_edge(da);
///
/// // NOW a and c should not be connected anymore:
/// assert!(!graph.is_connected(a, c));
/// ```
///
/// [1]: https://en.wikipedia.org/wiki/Dynamic_connectivity
/// [2]: https://en.wikipedia.org/wiki/Spanning_tree#Spanning_forests
/// [3]: https://en.wikipedia.org/wiki/Dynamic_connectivity#The_Level_structure
/// [4]: http://www.cs.princeton.edu/courses/archive/fall09/cos521/Handouts/polylogarithmic.pdf
///
#[derive(Clone, Debug)]
pub struct DynamicGraph<W = EmptyWeight>
where
    W: WeightType,
{
    size: usize,
    adjacency_hint: usize,
    max_level: usize,
    edges: DynamicEdgeList,
    euler: Vec<EulerForest<EmptyWeight>>,
    ext_euler: EulerForest<W>,
}

impl<W> DynamicGraph<W>
where
    W: WeightType,
{
    /// Construct a `DynamicGraph` with a fixed number of vertices, i.e. `size` and with an expected
    /// degree (i.e. number of adjacent edges) of `adjacency_hint`.
    ///
    /// For a given value of `size`, the `DynamicGraph` will accept the vertex indices from
    /// `VertexIndex(0)` to `VertexIndex(size-1)`. Values outside this range will be ignored by
    /// the methods taking a `VertexIndex`. Those methods, however, will not `panic` in this case
    /// but rather return `None`.
    ///
    /// Capacity to store edges incident to each vertex will be reserved according to the specified
    /// value of `adjacency_hint`. Re-allocation will occur if this capacity is exceeded.
    pub fn new(size: usize, adjacency_hint: usize) -> Self {
        let max_level = (size as f64).log2().floor() as usize;

        let mut euler = Vec::with_capacity(max_level + 1);
        for _ in 0..max_level + 1 {
            euler.push(EulerForest::new(size, adjacency_hint));
        }

        let edges = DynamicEdgeList::new(size * adjacency_hint);

        let ext_size = if size_of::<W>() == 0 { 0 } else { size };
        let ext_euler = EulerForest::new(ext_size, adjacency_hint);

        DynamicGraph {
            size,
            adjacency_hint,
            max_level,
            edges,
            euler,
            ext_euler,
        }
    }

    /// Returns the number of levels in the level structure of the HDT algorithm, that is
    /// for a graph `G = (V, E)`  with `|V| = n`, the number of levels will be
    /// `floor(log(n))`.
    pub fn max_level(&self) -> usize {
        self.max_level
    }

    /// Returns the number of vertices of this graph, that is for a graph `G = (V, E)`
    /// this method will return `|V| = n`.
    pub fn size(&self) -> usize {
        self.size
    }

    /// Returns the _initial_ capacity to store edges incident to each vertex
    /// (see also: [`new`](#method.new)).
    pub fn adjacency_hint(&self) -> usize {
        self.adjacency_hint
    }

    fn insert_tree_edge(&mut self, level: usize, e: EdgeIndex) {
        self.edges[e].is_tree_edge = true;
        self.edges[e].level = level;
        for i in (0..level + 1).rev() {
            self.euler[i].link(e, &self.edges);
        }
    }

    fn delete_tree_edge(&mut self, e: EdgeIndex) {
        self.edges[e].is_tree_edge = false;
        let level = self.edges[e].level;
        for i in (0..level + 1).rev() {
            self.euler[i].cut(e, &self.edges);
        }
    }

    fn insert_non_tree_edge(&mut self, level: usize, e: EdgeIndex) {
        self.edges[e].is_tree_edge = false;
        self.edges[e].level = level;

        let src = self.edges[e].src;
        let dst = self.edges[e].dst;

        self.euler[level].insert_adjacent_edge(src, e);
        self.euler[level].insert_adjacent_edge(dst, e);
    }

    fn delete_non_tree_edge(&mut self, e: EdgeIndex) {
        let src = self.edges[e].src;
        let dst = self.edges[e].dst;
        let level = self.edges[e].level;

        let s = self.euler[level]
            .adjacent_edge_index(src, e)
            .expect("delete_non_tree_edge(): find_none_tree_index(src) should never be None");
        self.euler[level].delete_adjacent_edge(src, s);

        let d = self.euler[level]
            .adjacent_edge_index(dst, e)
            .expect("delete_non_tree_edge(): find_none_tree_index(dst) should never be None");
        self.euler[level].delete_adjacent_edge(dst, d);
    }

    fn replace(&mut self, e: EdgeIndex) -> Option<EdgeIndex> {
        let src = self.edges[e].src;
        let dst = self.edges[e].dst;
        let e_level = self.edges[e].level;

        for level in (0..e_level + 1).rev() {
            let (smaller_tree, _) = self.euler[level].tree_roots_ordered(src, dst);

            let mut state = TreeEdgesState::new(&self.euler[level], smaller_tree);
            while let Some(e_tree) = state.next(&self.euler[level], &self.edges) {
                if self.edges[e_tree].level == level {
                    self.euler[level + 1].link(e_tree, &self.edges);
                    self.edges[e_tree].level = level + 1;
                }
            }
            let mut state = NonTreeEdgesState::new(&self.euler[level], smaller_tree);
            while let Some((v1, v1_idx)) = state.next(&self.euler[level]) {
                let e_nt_idx = self.euler[level].vertices[v1].adj_edges[v1_idx];
                let e_nt = self.edges[e_nt_idx];
                let v2 = if v1 == e_nt.src { e_nt.dst } else { e_nt.src };
                let v2_idx = self.euler[level]
                    .adjacent_edge_index(v2, e_nt_idx)
                    .expect("replace(): adjacent_edge_index() should never be None");

                self.euler[level].delete_adjacent_edge(v1, v1_idx);
                self.euler[level].delete_adjacent_edge(v2, v2_idx);

                let (src_tree, dst_tree) = self.euler[level].tree_roots(e_nt.src, e_nt.dst);

                if src_tree == dst_tree {
                    self.insert_non_tree_edge(level + 1, e_nt_idx);
                } else {
                    self.insert_tree_edge(level, e_nt_idx);
                    return Some(e_nt_idx);
                }
            }
        }
        None
    }
}

impl<W> DynamicConnectivity<W> for DynamicGraph<W>
where
    W: WeightType,
{
    /// Connects the vertices indexed by `v` and `w` and returns the index of the created edge.
    ///
    /// If the vertices cannot be connected `None` is returned. Vertices cannot be connected if
    /// `v` and `w` are equal or if either of them denotes an index greater or equal the
    /// [`size`](#method.size) of the `DynamicGraph`.
    ///
    /// ```
    /// use outils::prelude::*;
    ///
    /// // Construct a unweighted dynamic graph with a fixed number of 10 vertices with an expected
    /// // degree (i.e. number of adjacent edges) of 3.
    /// let mut graph: DynamicGraph<EmptyWeight> = DynamicGraph::new(10, 3);
    ///
    /// let a = VertexIndex(0);
    /// let b = VertexIndex(1);
    /// let c = VertexIndex(999); // Invalid vertex index!
    ///
    /// // Connect a and b:
    /// let ab = graph.insert_edge(a, b);
    /// assert!(ab.is_some());
    /// assert!(graph.is_connected(a, b));
    ///
    /// // Attempt to connect a and c, which is a vertex index greater than the size of the graph:
    /// let ac = graph.insert_edge(a, c);
    /// assert!(ac.is_none());
    /// assert!(!graph.is_connected(a, c));
    /// ```
    fn insert_edge(&mut self, v: VertexIndex, w: VertexIndex) -> Option<Edge> {
        if v == w || v.index() >= self.size || w.index() >= self.size {
            return None;
        }
        let e = self.edges.insert(DynamicEdge::new(v, w));
        if self.euler[0].is_connected(v, w) {
            self.insert_non_tree_edge(0, e);
        } else {
            self.insert_tree_edge(0, e);
            if size_of::<W>() > 0 {
                self.ext_euler.link(e, &self.edges);
            }
        }
        Some(Edge::new(e, v, w))
    }

    /// Deletes the edge `e` from the graph if it exists.
    ///
    /// **Note:** Usually, `e` should be an instance of an `Edge` that has been previously returned
    /// by [`insert_edge`](#method.insert_edge) and has not yet been deleted. This method will
    /// ignore any `Edge` passed to it that is not equal to an instance stored internally.
    fn delete_edge(&mut self, e: Edge) {
        let idx = e.index();
        if !self.edges.edges.contains(idx.index())
            || self.edges[idx].src != e.src()
            || self.edges[idx].dst != e.dst()
            {
                return;
            }
        if self.edges[idx].is_tree_edge {
            if size_of::<W>() > 0 {
                self.delete_tree_edge(idx);
                self.ext_euler.cut(idx, &self.edges);
                if let Some(edge) = self.replace(idx) {
                    self.ext_euler.link(edge, &self.edges);
                }
            } else {
                self.delete_tree_edge(idx);
                self.replace(idx);
            }
        } else {
            self.delete_non_tree_edge(idx);
        }
        self.edges.remove(idx);
    }

    /// Returns `true` if the two vertices indexed by `v` and `w` are connected in `self` through
    /// a path of edges.
    fn is_connected(&self, v: VertexIndex, w: VertexIndex) -> bool {
        if v == w || v.index() >= self.size || w.index() >= self.size {
            return false;
        }
        self.euler[0].is_connected(v, w)
    }
}

impl<'dc, W> DynamicComponent<'dc> for DynamicGraph<W>
    where
        W: WeightType,
{
    /// Returns a boxed iterator over the indices of the vertices which are connected to the
    /// vertex indexed by `v`.
    ///
    /// ```
    /// use outils::prelude::*;
    ///
    /// // Construct a unweighted dynamic graph with a fixed number of 10 vertices with an expected
    /// // degree (i.e. number of adjacent edges) of 3.
    /// let mut graph: DynamicGraph<EmptyWeight> = DynamicGraph::new(10, 3);
    ///
    /// let a = VertexIndex(0);
    /// let b = VertexIndex(1);
    /// let c = VertexIndex(2);
    /// let d = VertexIndex(3);
    ///
    /// // Connect a and b and c:
    /// let ab = graph.insert_edge(a, b);
    /// let ac = graph.insert_edge(a, c);
    ///
    /// let vertices: Vec<VertexIndex> = graph.component_vertices(b).collect();
    /// assert!(vertices.contains(&a));
    /// assert!(vertices.contains(&b));
    /// assert!(vertices.contains(&c));
    /// assert!(!vertices.contains(&d)); // d is not part of the component b belongs to!
    /// ```
    fn component_vertices(&'dc self, v: VertexIndex) -> Box<dyn Iterator<Item=VertexIndex> + 'dc> {
        Box::new(Vertices::new(
            &self.euler[0],
            self.euler[0].vertices[v].active_node,
        ))
    }

    /// Returns a boxed iterator over vertices that are representatives of connected components.
    /// This implies that no vertices returned by this iterator are connected to each other.
    ///
    /// ```
    /// use outils::prelude::*;
    ///
    /// // Construct a unweighted dynamic graph with a fixed number of 7 vertices with an expected
    /// // degree (i.e. number of adjacent edges) of 3.
    /// let mut graph: DynamicGraph<EmptyWeight> = DynamicGraph::new(7, 3);
    ///
    /// let a = VertexIndex(0);
    /// let b = VertexIndex(1);
    /// let c = VertexIndex(2);
    /// let d = VertexIndex(3);
    /// let e = VertexIndex(4);
    /// let f = VertexIndex(5);
    /// let g = VertexIndex(6);
    ///
    /// //Create four components: {a, b}, {c, d}, {e, f} and {g}
    /// graph.insert_edge(a, b);
    /// graph.insert_edge(c, d);
    /// graph.insert_edge(e, f);
    ///
    /// // Expect exactly one vertex of each component to be included by the components iterator:
    /// let vertices: Vec<VertexIndex> = graph.components().collect();
    /// assert!(vertices.contains(&a) || vertices.contains(&b));
    /// assert!(vertices.contains(&c) || vertices.contains(&d));
    /// assert!(vertices.contains(&e) || vertices.contains(&f));
    /// assert!(vertices.contains(&g));
    /// ```
    fn components(&'dc self) -> Box<dyn Iterator<Item=VertexIndex> + 'dc> {
        Box::new(
            self.euler[0]
                .forest
                .values()
                .filter(move |&(n, _v)| self.euler[0].forest.parent(n).is_none())
                .map(move |(n, _v)| self.euler[0].forest[n].vertex),
        )
    }

    /// Returns a boxed iterator over the indices of the edges which connect the component the
    /// vertex indexed by `v` is part of.
    ///
    /// ```
    /// use outils::prelude::*;
    ///
    /// // Construct a unweighted dynamic graph with a fixed number of 10 vertices with an expected
    /// // degree (i.e. number of adjacent edges) of 3.
    /// let mut graph: DynamicGraph<EmptyWeight> = DynamicGraph::new(10, 3);
    ///
    /// let a = VertexIndex(0);
    /// let b = VertexIndex(1);
    /// let c = VertexIndex(2);
    /// let d = VertexIndex(3);
    /// let e = VertexIndex(4);
    /// let f = VertexIndex(5);
    /// let g = VertexIndex(6);
    ///
    /// //Create component: {a, b, c, d}
    /// let ab = graph.insert_edge(a, b).expect("No reason to fail here");
    /// let bc = graph.insert_edge(b, c).expect("No reason to fail here");
    /// let bd = graph.insert_edge(b, d).expect("No reason to fail here");
    /// let da = graph.insert_edge(a, b).expect("No reason to fail here"); // Non-spanning edge!
    ///
    /// //Create component: {e, f, g}
    /// let ef = graph.insert_edge(e, f).expect("No reason to fail here");
    /// let gf = graph.insert_edge(g, f).expect("No reason to fail here");
    /// let eg = graph.insert_edge(e, g).expect("No reason to fail here"); // Non-spanning edge!
    ///
    /// let abcd_edges: Vec<Edge> = graph.component_edges(a).collect();
    /// assert!(abcd_edges.contains(&ab));
    /// assert!(abcd_edges.contains(&bc));
    /// assert!(abcd_edges.contains(&bd));
    /// assert!(abcd_edges.contains(&da));
    ///
    /// let efg_edges: Vec<Edge> = graph.component_edges(e).collect();
    /// assert!(efg_edges.contains(&ef));
    /// assert!(efg_edges.contains(&gf));
    /// assert!(efg_edges.contains(&eg));
    /// ```
    fn component_edges(&'dc self, v: VertexIndex) -> Box<dyn Iterator<Item=Edge> + 'dc> {
        Box::new(
            Vertices::new(&self.euler[0], self.euler[0].vertices[v].active_node).flat_map(
                move |v| {
                    self.euler[0].vertices[v]
                        .tree_edges
                        .iter()
                        .map(|he| he.1.edge)
                        .chain(
                            self.euler
                                .iter()
                                .flat_map(move |f| f.vertices[v].adj_edges.iter().cloned()),
                        )
                        .map(move |e| Edge::new(e, self.edges[e].src, self.edges[e].dst))
                        .filter(move |t| t.src() == v)
                },
            ),
        )
    }

    /// Deletes all edges from this graph which connect the component the
    /// vertex indexed by `v` is part of.
    ///
    /// Generally, this operation will be significantly faster than calling `delete_edge` on each
    /// edge of the component separately, the reason being that it is not necessary to attempt to
    /// to reconnect the component with replacement edges when it is known beforehand that every
    /// edge of the component is going to be deleted.
    ///
    /// ```
    /// use outils::prelude::*;
    ///
    /// // Construct a unweighted dynamic graph with a fixed number of 10 vertices with an expected
    /// // degree (i.e. number of adjacent edges) of 3.
    /// let mut graph: DynamicGraph<EmptyWeight> = DynamicGraph::new(10, 3);
    ///
    /// let a = VertexIndex(0);
    /// let b = VertexIndex(1);
    /// let c = VertexIndex(2);
    /// let d = VertexIndex(3);
    ///
    /// //Create component: {a, b, c, d}
    /// let ab = graph.insert_edge(a, b).expect("No reason to fail here");
    /// let bc = graph.insert_edge(b, c).expect("No reason to fail here");
    /// let bd = graph.insert_edge(b, d).expect("No reason to fail here");
    /// let da = graph.insert_edge(a, b).expect("No reason to fail here"); // Non-spanning edge!
    ///
    /// let abcd_edges: Vec<Edge> = graph.disconnect_component(a);
    /// assert!(abcd_edges.contains(&ab));
    /// assert!(abcd_edges.contains(&bc));
    /// assert!(abcd_edges.contains(&bd));
    /// assert!(abcd_edges.contains(&da));
    ///
    /// assert!(!graph.is_connected(a, b));
    /// assert!(!graph.is_connected(a, c));
    /// assert!(!graph.is_connected(a, d));
    /// assert!(!graph.is_connected(b, c));
    /// assert!(!graph.is_connected(b, d));
    /// assert!(!graph.is_connected(c, d));
    /// ```
    fn disconnect_component(&mut self, v: VertexIndex) -> Vec<Edge> {
        let edges: Vec<Edge> = self.component_edges(v).collect();
        for e in &edges {
            let idx = e.index();
            if self.edges[idx].is_tree_edge {
                if size_of::<W>() > 0 {
                    self.delete_tree_edge(idx);
                    self.ext_euler.cut(idx, &self.edges);
                } else {
                    self.delete_tree_edge(idx);
                }
            } else {
                self.delete_non_tree_edge(idx);
            }
            self.edges.remove(idx);
        }
        edges
    }
}

impl<W> DynamicWeightedComponent<W> for DynamicGraph<W>
where
    W: WeightType,
{
    /// Set the weight of the vertex indexed by `v` to `weight` and update the weight of the
    /// component this vertex belongs to. If `v` was a valid index, the old weight is returned.
    ///
    /// ```
    /// use outils::prelude::*;
    ///
    /// // Construct a dynamic graph with weights of type usize and a fixed number of 10 vertices
    /// // with an expected degree (i.e. number of adjacent edges) of 3.
    /// let mut graph: DynamicGraph<usize> = DynamicGraph::new(10, 3);
    ///
    /// let a = VertexIndex(0);
    /// assert_eq!(graph.set_vertex_weight(a, 2), Some(0));
    /// ```
    fn set_vertex_weight(&mut self, v: VertexIndex, weight: W) -> Option<W> {
        if size_of::<W>() > 0 && v.index() < self.size {
            let n = self.ext_euler.vertices[v].active_node;
            let old_weight = self.ext_euler.forest.weight(n).cloned();
            self.ext_euler
                .forest
                .adjust_weight(n, &|w: &mut VertexWeight<W>| (*w).weight = weight);
            return old_weight.map(|w| w.weight);
        }
        None
    }

    /// Immutably access the weight of the vertex indexed by `v`.
    fn vertex_weight(&self, v: VertexIndex) -> Option<&W> {
        if size_of::<W>() > 0 && v.index() < self.size {
            let n = self.ext_euler.vertices[v].active_node;
            self.ext_euler.forest.weight(n).map(|w| &w.weight)
        } else {
            None
        }
    }

    /// Immutably access the weight of the component to which the vertex indexed by `v` belongs.
    ///
    /// ```
    /// use outils::prelude::*;
    ///
    /// // Construct a dynamic graph with weights of type usize and a fixed number of 10 vertices
    /// // with an expected degree (i.e. number of adjacent edges) of 3.
    /// let mut graph: DynamicGraph<usize> = DynamicGraph::new(10, 3);
    ///
    /// let a = VertexIndex(0);
    /// let b = VertexIndex(1);
    /// let c = VertexIndex(2);
    /// let d = VertexIndex(3);
    ///
    /// graph.set_vertex_weight(a, 1);
    /// graph.set_vertex_weight(b, 1);
    /// graph.set_vertex_weight(c, 1);
    /// graph.set_vertex_weight(d, 1);
    ///
    /// // Create component {a, b, c, d} - since all vertices have a weight of 1, the resulting
    /// // component should have a weight of 4.
    /// let ab = graph.insert_edge(a, b).expect("No reason to fail here");
    /// let bc = graph.insert_edge(b, c).expect("No reason to fail here");
    /// let bd = graph.insert_edge(b, d).expect("No reason to fail here");
    /// let da = graph.insert_edge(a, b).expect("No reason to fail here"); // Non-spanning edge!
    ///
    /// assert_eq!(graph.component_weight(a), Some(&4));
    /// ```
    fn component_weight(&self, v: VertexIndex) -> Option<&W> {
        if size_of::<W>() > 0 && v.index() < self.size {
            let n = self.ext_euler.vertices[v].active_node;
            let root = self.ext_euler.forest.root(n);
            match root {
                Some(rt) => {
                    return self.ext_euler.forest.subweight(rt).map(|w| &w.weight);
                }
                None => {
                    return None;
                }
            }
        }
        None
    }

    /// Change the weight of the vertex indexed by `v` by applying the closure `f`. After applying
    /// the closure, the weight of the component this vertex belongs to will be updated accordingly.
    /// If `v` was a valid index a reference to the changed weight is returned.
    ///
    /// ```
    /// use outils::prelude::*;
    ///
    /// // Construct a dynamic graph with weights of type usize and a fixed number of 10 vertices
    /// // with an expected degree (i.e. number of adjacent edges) of 3.
    /// let mut graph: DynamicGraph<usize> = DynamicGraph::new(10, 3);
    ///
    /// let a = VertexIndex(0);
    /// assert_eq!(graph.adjust_vertex_weight(a, &|w: &mut usize| *w += 2), Some(&2));
    /// ```
    fn adjust_vertex_weight(&mut self, v: VertexIndex, f: &dyn Fn(&mut W)) -> Option<&W> {
        if size_of::<W>() > 0 && v.index() < self.size {
            let n = self.ext_euler.vertices[v].active_node;
            return self
                .ext_euler
                .forest
                .adjust_weight(n, &|w: &mut VertexWeight<W>| f(&mut w.weight))
                .map(|w| &w.weight);
        }
        None
    }
}

impl<'slf, W> Edges<'slf> for DynamicGraph<W>
    where
        W: WeightType,
{
    fn edges(&'slf self) -> Box<dyn Iterator<Item=Edge> + 'slf> {
        Box::new(
            self.edges
                .edges
                .iter()
                .map(|(i, e)| Edge::new(EdgeIndex(i), e.src, e.dst)),
        )
    }
}

struct VerticesState<W> {
    stack: Vec<NodeIndex>,
    size_hint: (usize, Option<usize>),
    _phantom: PhantomData<W>,
}

impl<W> VerticesState<W>
where
    W: WeightType,
{
    fn new(euler: &EulerForest<W>, node: NodeIndex) -> Self {
        let mut min_size = 0;
        let mut max_size = 0;
        let mut v;
        let f = &euler.forest;
        if let Some(rt) = f.root(node) {
            min_size = 1;
            max_size = f.subweight(rt).map_or(0, |w| w.act_count);
            let stack_hint = (((max_size * 2) - 1) as f64).log2().floor() as usize;
            v = Vec::with_capacity(stack_hint);
            v.push(rt);
        } else {
            v = Vec::with_capacity(0);
        }
        VerticesState {
            stack: v,
            size_hint: (min_size, Some(max_size)),
            _phantom: PhantomData,
        }
    }

    fn next(&mut self, euler: &EulerForest<W>) -> Option<VertexIndex> {
        let f = &euler.forest;
        loop {
            if let Some(n) = self.stack.pop() {
                if let Some(c) = f.child(n, 1) {
                    if f.subweight(c).map_or(0, |w| w.act_count) > 0 {
                        self.stack.push(c)
                    }
                }
                if let Some(c) = f.child(n, 0) {
                    if f.subweight(c).map_or(0, |w| w.act_count) > 0 {
                        self.stack.push(c)
                    }
                }
                if f.weight(n).map_or(0, |w| w.act_count) == 1 {
                    return Some(f[n].vertex);
                }
            } else {
                return None;
            }
        }
    }
}

struct Vertices<'dc, W>
    where
        W: 'dc + WeightType,
{
    euler: &'dc EulerForest<W>,
    state: VerticesState<W>,
}

impl<'dc, W> Vertices<'dc, W>
    where
        W: 'dc + WeightType,
{
    fn new(euler: &'dc EulerForest<W>, node: NodeIndex) -> Self {
        Vertices {
            euler,
            state: VerticesState::new(euler, node),
        }
    }
}

impl<'dc, W> Iterator for Vertices<'dc, W>
    where
        W: 'dc + WeightType,
{
    type Item = VertexIndex;
    fn next(&mut self) -> Option<VertexIndex> {
        self.state.next(self.euler)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.state.size_hint
    }
}

struct TreeEdgesState<W>
where
    W: WeightType,
{
    stack: Vec<NodeIndex>,
    _phantom: PhantomData<W>,
}

impl<W> TreeEdgesState<W>
where
    W: WeightType,
{
    fn new(euler: &EulerForest<W>, node: NodeIndex) -> Self {
        let mut v;
        let f = &euler.forest;
        if let Some(rt) = f.root(node) {
            let max_size = f.subweight(rt).map_or(0, |w| w.act_count) - 1;
            let stack_hint = ((((max_size + 1) * 2) - 1) as f64).log2().floor() as usize;
            v = Vec::with_capacity(stack_hint);
            v.push(rt);
        } else {
            v = Vec::with_capacity(0);
        }
        TreeEdgesState {
            stack: v,
            _phantom: PhantomData,
        }
    }

    fn next(&mut self, euler: &EulerForest<W>, edges: &DynamicEdgeList) -> Option<EdgeIndex> {
        let f = &euler.forest;
        loop {
            if let Some(n) = self.stack.pop() {
                if let Some(c) = f.child(n, 1) {
                    self.stack.push(c)
                }
                if let Some(c) = f.child(n, 0) {
                    self.stack.push(c)
                }
                if let Some(h_out) = f[n][EdgeDirection::Outgoing] {
                    let v = f[n].vertex;
                    let e = euler.vertices[v].tree_edges[h_out].edge;
                    if edges[e].src == v {
                        return Some(e);
                    }
                }
            } else {
                return None;
            }
        }
    }
}

struct NonTreeEdgesState<W>
where
    W: WeightType,
{
    stack: Vec<NodeIndex>,
    vertex: Option<VertexIndex>,
    idx: usize,
    _phantom: PhantomData<W>,
}

impl<W> NonTreeEdgesState<W>
where
    W: WeightType,
{
    fn new(euler: &EulerForest<W>, node: NodeIndex) -> Self {
        let mut v;
        let f = &euler.forest;
        if let Some(rt) = f.root(node) {
            let mut stack_hint = f.subweight(rt).map_or(0, |w| w.act_count);
            stack_hint = (((stack_hint * 2) - 1) as f64).log2().floor() as usize;
            v = Vec::with_capacity(stack_hint);
            v.push(rt);
        } else {
            v = Vec::with_capacity(0);
        }
        NonTreeEdgesState {
            stack: v,
            vertex: None,
            idx: 0,
            _phantom: PhantomData,
        }
    }

    fn next(&mut self, euler: &EulerForest<W>) -> Option<(VertexIndex, usize)> {
        let f = &euler.forest;
        loop {
            if self.idx == 0 {
                if let Some(n) = self.stack.pop() {
                    if let Some(c) = f.child(n, 1) {
                        if f.subweight(c).map_or(0, |w| w.adj_count) > 0 {
                            self.stack.push(c)
                        }
                    }
                    if let Some(c) = f.child(n, 0) {
                        if f.subweight(c).map_or(0, |w| w.adj_count) > 0 {
                            self.stack.push(c)
                        }
                    }
                    if f.weight(n).map_or(0, |w| w.act_count) == 1 {
                        let v = f[n].vertex;
                        self.vertex = Some(v);
                        self.idx = euler.vertices[v].adj_edges.len();
                    }
                } else {
                    return None;
                }
            } else {
                self.idx -= 1;
                let v = self
                    .vertex
                    .expect("AdjecentEdgeIteratorState::next(): self.vertex should not be None");
                return Some((v, self.idx));
            }
        }
    }
}
