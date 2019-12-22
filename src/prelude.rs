//! Commonly used items.
//!
//! ```
//! use outils::prelude::*;
//! ```
#[doc(no_inline)]
pub use crate::graph::dynconn::{DynamicComponent, DynamicConnectivity, DynamicWeightedComponent};
#[doc(no_inline)]
pub use crate::graph::dynconn::hdt::DynamicGraph;
#[doc(no_inline)]
pub use crate::tree::bst::{BalancedBinaryForest, BinarySearchTree, BstDirection, OrderedTree};
#[doc(no_inline)]
pub use crate::tree::bst::aaforest::AaForest;
#[doc(no_inline)]
pub use crate::tree::bst::aatree::AaTree;
#[doc(no_inline)]
pub use crate::tree::bst::waaforest::WeightedAaForest;
#[doc(no_inline)]
pub use crate::tree::bst::waatree::WeightedAaTree;
#[doc(no_inline)]
pub use crate::tree::generic::{Forest, GenericForest};
#[doc(no_inline)]
pub use crate::tree::traversal::Traversable;
#[doc(no_inline)]
pub use crate::tree::WeightedTree;
#[doc(no_inline)]
pub use crate::types::{
    Children, Edge, EdgeIndex, Edges, EmptyWeight, IndexType, Keys, KeyType, NodeIndex, Values,
    ValueType, VertexIndex, WeightType,
};
