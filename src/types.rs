//! Types that are the basic building blocks of the types and algorithms provided by this library.
use core::hash::Hash;
use std::fmt::Debug;
use std::ops::{Add, AddAssign};

/// The default implementation of `IndexType` is `usize`.
pub type DefaultIndexType = usize;
/// The default implementation of `WeightType` is `usize`.
pub type DefaultWeightType = usize;

/// Super trait for types that are supported as tree node, vertex and egde indices.
/// This trait is implemented automatically for all types implementing the base traits
pub trait IndexType: Default + Debug + Copy + Eq + Ord + Hash {}

/// Super trait for types that are supported as search keys.
/// This trait is implemented automatically for all types implementing the base traits
pub trait KeyType: Default + Debug + Copy + Eq + Ord + Hash {}

/// Super trait for types that are supported as values to be stored in the structs provided by
/// this library. This trait is implemented automatically for all types implementing the base traits
pub trait ValueType: Default + Debug + Hash {}

/// Super trait for types that are supported as tree node and vertex weights.
/// This trait is implemented automatically for all types implementing the base traits
///
/// **Note:** In order for the algorithms in this library to work correctly, the implementation of
/// `Default` must yield the neutral element to the operations of `Add` and `AddAssign`.
pub trait WeightType: Default + Debug + Copy + Hash + Eq + Ord + Add<Output=Self> + AddAssign {}

impl<T> IndexType for T
where
    T: Default + Debug + Copy + Eq + Ord + Hash,
{
}

impl<T> KeyType for T
where
    T: Default + Debug + Copy + Eq + Ord + Hash,
{
}

impl<T> ValueType for T
where
    T: Default + Debug + Hash,
{
}

impl<T> WeightType for T
where
    T: Default + Debug + Copy + Hash + Eq + Ord + Add<Output=Self> + AddAssign,
{
}

/// Unit-like (i.e. zero-sized) struct that can be used as a `WeightType`.
#[derive(Debug, Copy, Clone, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub struct EmptyWeight;

impl Default for EmptyWeight {
    fn default() -> Self {
        EmptyWeight
    }
}

impl Add for EmptyWeight {
    type Output = EmptyWeight;

    fn add(self, _other: EmptyWeight) -> EmptyWeight {
        EmptyWeight
    }
}

impl AddAssign for EmptyWeight {
    fn add_assign(&mut self, _other: EmptyWeight) {}
}

/// Newtype to be used as a type-safe tree node identifier
#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct NodeIndex<Ix = DefaultIndexType>(pub Ix);

impl<Ix> NodeIndex<Ix>
where
    Ix: IndexType,
{
    #[inline]
    pub fn index(&self) -> Ix {
        self.0
    }
}

impl<Ix> From<Ix> for NodeIndex<Ix>
where
    Ix: IndexType,
{
    fn from(ix: Ix) -> Self {
        NodeIndex(ix)
    }
}

/// Newtype to be used as a type-safe vertex identifier
#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct VertexIndex<Ix = DefaultIndexType>(pub Ix);

impl<Ix> VertexIndex<Ix>
where
    Ix: IndexType,
{
    #[inline]
    pub fn index(&self) -> Ix {
        self.0
    }
}

impl<Ix> From<Ix> for VertexIndex<Ix>
where
    Ix: IndexType,
{
    fn from(ix: Ix) -> Self {
        VertexIndex(ix)
    }
}

/// Newtype to be used as a type-safe edge identifier
#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct EdgeIndex<Ix = DefaultIndexType>(pub Ix);

impl<Ix> EdgeIndex<Ix>
where
    Ix: IndexType,
{
    #[inline]
    pub fn index(&self) -> Ix {
        self.0
    }
}

impl<Ix> From<Ix> for EdgeIndex<Ix>
where
    Ix: IndexType,
{
    fn from(ix: Ix) -> Self {
        EdgeIndex(ix)
    }
}

/// Trees implementing this trait are able to return an iterator over the search keys held by
/// the implementing struct.
pub trait Keys<'slf, K, Ix = DefaultIndexType>
where
    K: 'slf + KeyType,
    Ix: IndexType,
{
    /// Returns a boxed iterator over the search keys and their corresponding
    /// tree node indices held by `self`.
    fn keys(&'slf self) -> Box<Iterator<Item=(NodeIndex<Ix>, &'slf K)> + 'slf>;
}

/// Trees implementing this trait are able to return an iterator over the values stored by
/// the implementing struct.
pub trait Values<'slf, V, Ix = DefaultIndexType>
where
    V: 'slf + ValueType,
    Ix: IndexType,
{
    /// Returns a boxed iterator over the stored values and their corresponding
    /// tree node indices held by `self`.
    fn values(&'slf self) -> Box<Iterator<Item=(NodeIndex<Ix>, &'slf V)> + 'slf>;
}

/// Graphs implementing this trait are able to return an iterator over the indices of
/// their vertices.
pub trait Vertices<'slf, Ix = DefaultIndexType>
where
    Ix: IndexType,
{
    /// Returns a boxed iterator over the indices or the vertices held by `self`.
    fn vertices(&'slf self) -> Box<Iterator<Item = VertexIndex<Ix>> + 'slf>;
}

/// Graphs implementing this trait are able to return an iterator over the indices of
/// their edges.
pub trait Edges<'slf, Ix = DefaultIndexType>
where
    Ix: IndexType,
{
    /// Returns a boxed iterator over the indices or the edges held by `self`, along with
    /// their associated vertex indices.
    fn edges(
        &'slf self,
    ) -> Box<Iterator<Item=(EdgeIndex<Ix>, VertexIndex<Ix>, VertexIndex<Ix>)> + 'slf>;
}

/// Trees and graphs implementing this trait are able to export a [TGF][1] representation
/// of themselves, using debug formatting for tree node, vertex and edge contents.
///
/// [1]: https://en.wikipedia.org/wiki/Trivial_Graph_Format
pub trait Tgf {
    /// Returns a TGF representation of `Self`.
    fn to_tgf(&self) -> String;
}
