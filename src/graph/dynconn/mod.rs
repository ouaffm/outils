//!
//! Graph data structures and algorithms providing dynamic connectivity
//!
use types::{DefaultIndexType, Edge, EmptyWeight, IndexType, VertexIndex, WeightType};

pub mod hdt;

/// This trait defines the fundamental operations of a _dynamic graph_, that is a graph providing
/// a fully dynamic connectivity interface.
///
/// A _dynamic graph_ data structure is able to answer queries as to whether two vertices are
/// connected in a graph through a path of edges. In this context, _fully dynamic_ means that
/// the graph can be updated by insertions or deletions of edges between queries
/// (see also [Dynamic Connectivity][1]).
///
/// [1]: https://en.wikipedia.org/wiki/Dynamic_connectivity
pub trait DynamicConnectivity<W = EmptyWeight, Ix = DefaultIndexType>
where
    Ix: IndexType,
{
    /// Connects the vertices indexed by `v` and `w` and returns index of the created edge.
    /// If the vertices cannot be connected - the reasons for this dependant on the implementation
    /// of this trait - `None` is returned.
    fn insert_edge(&mut self, v: VertexIndex<Ix>, w: VertexIndex<Ix>) -> Option<Edge<Ix>>;

    /// Deletes the edge  `e` from the graph if it exists.
    fn delete_edge(&mut self, e: Edge<Ix>);

    /// Returns `true` if the two vertices indexed by `v` and `w` are connected in `self` through
    /// a path of edges.
    fn is_connected(&self, v: VertexIndex<Ix>, w: VertexIndex<Ix>) -> bool;
}

/// This trait defines the fundamental operations of a _dynamic graph_, that can be applied to
/// a connected sub-graph, that is, the connected components of the graph.
pub trait DynamicComponent<'a, Ix = DefaultIndexType>
where
    Ix: IndexType,
{
    /// Returns a boxed iterator over the indices of the vertices which are connected to the
    /// vertex indexed by `v`.
    fn component_vertices(
        &'a self,
        v: VertexIndex<Ix>,
    ) -> Box<Iterator<Item = VertexIndex<Ix>> + 'a>;

    /// Returns a boxed iterator over vertices that are representatives of connected components.
    /// This implies that no vertices returned by this iterator are connected to each other.
    fn components(&'a self) -> Box<Iterator<Item=VertexIndex<Ix>> + 'a>;

    /// Returns a boxed iterator over the indices of the edges which connect the component the
    /// vertex indexed by `v` is part of.
    fn component_edges(&'a self, v: VertexIndex<Ix>) -> Box<Iterator<Item=Edge> + 'a>;

    /// Deletes all edges from this graph which connect the component the
    /// vertex indexed by `v` is part of.
    fn disconnect_component(&mut self, v: VertexIndex<Ix>) -> Vec<Edge>;
}

/// This trait defines the fundamental operations of a _dynamic graph_ related to vertex weights,
/// that can be applied to a connected sub-graph, that is, the connected components of the graph.
pub trait DynamicWeightedComponent<W = EmptyWeight, Ix = DefaultIndexType>
where
    W: WeightType,
    Ix: IndexType,
{
    /// Set the weight of the vertex indexed by `v` to `weight` and update the weight of the
    /// component this vertex belongs to. If `v` was a valid index, the old weight is returned.
    fn set_vertex_weight(&mut self, v: VertexIndex<Ix>, weight: W) -> Option<W>;

    /// Immutably access the weight of the vertex indexed by `v`.
    fn vertex_weight(&self, v: VertexIndex<Ix>) -> Option<&W>;

    /// Immutably access the weight of the component to which the vertex indexed by `v` belongs.
    fn component_weight(&self, v: VertexIndex<Ix>) -> Option<&W>;

    /// Change the weight of the vertex indexed by `v` by applying the closure `f`. After applying
    /// the closure, the weight of the component this vertex belongs to will be updated accordingly.
    /// If `v` was a valid index a reference to the changed weight is returned.
    fn adjust_vertex_weight(&mut self, v: VertexIndex<Ix>, f: &Fn(&mut W)) -> Option<&W>;
}
