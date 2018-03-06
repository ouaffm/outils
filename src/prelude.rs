//! Commonly used items.
//!
//! ```
//! use outils::prelude::*;
//! ```

#[doc(no_inline)]
pub use types::{EdgeIndex, EmptyWeight, IndexType, KeyType, Keys, NodeIndex, ValueType, Values,
                VertexIndex, WeightType};

#[doc(no_inline)]
pub use tree::WeightedTree;

#[doc(no_inline)]
pub use tree::traversal::Traversable;

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
