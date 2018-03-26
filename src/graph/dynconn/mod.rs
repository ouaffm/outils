use types::{DefaultIndexType, EdgeIndex, EmptyWeight, IndexType, VertexIndex, WeightType};

pub mod hdt;

pub trait DynamicConnectivity<W = EmptyWeight, Ix = DefaultIndexType>
where
    Ix: IndexType,
{
    fn insert_edge(&mut self, v: VertexIndex<Ix>, w: VertexIndex<Ix>) -> Option<EdgeIndex<Ix>>;
    fn delete_edge(&mut self, e: EdgeIndex<Ix>);
    fn is_connected(&self, v: VertexIndex<Ix>, w: VertexIndex<Ix>) -> bool;
}

pub trait DynamicComponent<'a, Ix = DefaultIndexType>
where
    Ix: IndexType,
{
    fn component_vertices(
        &'a self,
        v: VertexIndex<Ix>,
    ) -> Box<Iterator<Item = VertexIndex<Ix>> + 'a>;

    fn components(&'a self) -> Box<Iterator<Item=VertexIndex<Ix>> + 'a>;

    fn component_edges(
        &'a self,
        v: VertexIndex<Ix>,
    ) -> Box<Iterator<Item = (EdgeIndex<Ix>, VertexIndex<Ix>, VertexIndex<Ix>)> + 'a>;
}

pub trait DynamicWeightedComponent<W = EmptyWeight, Ix = DefaultIndexType>
where
    W: WeightType,
    Ix: IndexType,
{
    fn set_vertex_weight(&mut self, v: VertexIndex<Ix>, weight: W);
    fn vertex_weight(&self, v: VertexIndex<Ix>) -> Option<&W>;
    fn component_weight(&self, v: VertexIndex<Ix>) -> Option<&W>;
}
