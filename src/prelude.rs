//! Commonly used items.
//!
//! ```
//! use outils::prelude::*;
//! ```
#[doc(no_inline)]
pub use graph::dynconn::{DynamicComponent, DynamicConnectivity, DynamicWeightedComponent};
#[doc(no_inline)]
pub use graph::dynconn::hdt::DynamicGraph;
#[doc(no_inline)]
pub use tree::bst::{BalancedBinaryForest, BinarySearchTree, BstDirection, OrderedTree};
#[doc(no_inline)]
pub use tree::bst::aaforest::AaForest;
#[doc(no_inline)]
pub use tree::bst::aatree::AaTree;
#[doc(no_inline)]
pub use tree::bst::waaforest::WeightedAaForest;
#[doc(no_inline)]
pub use tree::bst::waatree::WeightedAaTree;
#[doc(no_inline)]
pub use tree::generic::{Forest, GenericForest};
#[doc(no_inline)]
pub use tree::traversal::Traversable;
#[doc(no_inline)]
pub use tree::WeightedTree;
#[doc(no_inline)]
pub use types::{
    Children, Edge, EdgeIndex, Edges, EmptyWeight, IndexType, Keys, KeyType, NodeIndex, Values,
    ValueType, VertexIndex, WeightType,
};
