use std::fmt::Debug;
use std::ops::{Add, AddAssign};

pub type DefaultIndexType = usize;
pub type DefaultWeightType = usize;

pub trait IndexType: Default + Debug + Copy + Ord {}
pub trait KeyType: Default + Debug + Copy + Ord {}
pub trait ValueType: Default + Debug {}
pub trait WeightType: Default + Debug + Copy + Add<Output = Self> + AddAssign {}

impl<T> IndexType for T
where
    T: Default + Debug + Copy + Ord,
{
}

impl<T> KeyType for T
where
    T: Default + Debug + Copy + Ord,
{
}

impl<T> ValueType for T
where
    T: Default + Debug,
{
}

impl<T> WeightType for T
where
    T: Default + Debug + Copy + Add<Output = Self> + AddAssign,
{
}

#[derive(Debug, Copy, Clone)]
pub struct EmptyWeight(());

impl Default for EmptyWeight {
    fn default() -> Self {
        EmptyWeight(())
    }
}

impl Add for EmptyWeight {
    type Output = EmptyWeight;

    fn add(self, _other: EmptyWeight) -> EmptyWeight {
        EmptyWeight(())
    }
}

impl AddAssign for EmptyWeight {
    fn add_assign(&mut self, _other: EmptyWeight) {}
}

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

pub trait Keys<'slf, K>
where
    K: 'slf + KeyType,
{
    fn keys(&'slf self) -> Box<Iterator<Item = &'slf K> + 'slf>;
}

pub trait Values<'slf, V>
where
    V: 'slf + ValueType,
{
    fn values(&'slf self) -> Box<Iterator<Item = &'slf V> + 'slf>;
}

pub trait Vertices<'slf, Ix = DefaultIndexType>
where
    Ix: IndexType,
{
    fn vertices(&'slf self) -> Box<Iterator<Item = VertexIndex<Ix>> + 'slf>;
}

pub trait Edges<'slf, Ix = DefaultIndexType>
where
    Ix: IndexType,
{
    fn edges(&'slf self) -> Box<Iterator<Item = EdgeIndex<Ix>> + 'slf>;
}
