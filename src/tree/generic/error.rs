//!
//! `TreeError<Ix>` is the error type for the operations of the [`GenericForest`][1] trait.
//!
//! [1]: ../trait.GenericForest.html
use std::error::Error;
use std::fmt;
use std::string::String;
use super::*;

/// Enum to refer to error situations that commonly occur in forest operations.
#[derive(Clone, Debug)]
pub enum TreeErrorType<Ix = DefaultIndexType> {
    /// A node index was passed to an operation but did not refer to a valid node.
    InvalidNodeIndex {
        /// The node index that was passed to the operation.
        node: NodeIndex<Ix>,
    },
    /// An operation is only defined for root nodes, but an invalid node index or a node index
    /// referring to a non-tree node was passed to the operation.
    ExpectedRootNode {
        /// The node index that was passed to operation.
        node: NodeIndex<Ix>,
    },
    /// An operation is only defined for forest nodes that are not part of the same forest tree,
    /// but the nodes passed to this operation are already in a ancestor/descendant relation.
    ExpectedNonAncestorNode {
        /// The node that was passed to the operation as the new ancestor
        new_ancestor: NodeIndex<Ix>,
        /// The node that was passed to the operation as the new descendant
        new_descendant: NodeIndex<Ix>,
    },
    /// Summary error type, which can be used in other error situations which do not have a
    /// direct relation to defined operations of a forest.
    OtherError {
        /// Description of the particular error situation.
        msg: String,
    },
}

/// Error type that covers the error situations that commonly occur when manipulation tree or
/// forest operations.
///
/// `TreeError` keeps a `TreeErrorType` describing the error as well as a `String` that can be
/// used to store a description of the context in which the error has occured.
#[derive(Clone, Debug)]
pub struct TreeError<Ix = DefaultIndexType> {
    context: String,
    error: TreeErrorType<Ix>,
}

impl<Ix> TreeError<Ix> {
    /// Construct a new `TreeError` of type `TreeErrorType::InvalidNodeIndex` referring to `node`
    pub fn invalid_node_index(context: &str, node: NodeIndex<Ix>) -> Self {
        TreeError {
            context: String::from(context),
            error: TreeErrorType::InvalidNodeIndex { node },
        }
    }

    /// Construct a new `TreeError` of type `TreeErrorType::ExpectedRootNode` referring to `node`
    pub fn expected_root_node(context: &str, node: NodeIndex<Ix>) -> Self {
        TreeError {
            context: String::from(context),
            error: TreeErrorType::ExpectedRootNode { node },
        }
    }

    /// Construct a new `TreeError` of type `TreeErrorType::ExpectedNonAncestorNode` referring to
    /// `new_ancestor` and `new_descendant`.
    pub fn expected_non_ancestor_node(
        context: &str,
        new_ancestor: NodeIndex<Ix>,
        new_descendant: NodeIndex<Ix>,
    ) -> Self {
        TreeError {
            context: String::from(context),
            error: TreeErrorType::ExpectedNonAncestorNode {
                new_ancestor,
                new_descendant,
            },
        }
    }

    /// Construct a new `TreeError` of type `TreeErrorType::OtherType` with a custom message
    /// `msg`describing the particular error situation.
    pub fn other_error(context: &str, msg: &str) -> Self {
        TreeError {
            context: String::from(context),
            error: TreeErrorType::OtherError {
                msg: String::from(msg),
            },
        }
    }
}

impl fmt::Display for TreeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.error {
            TreeErrorType::InvalidNodeIndex { node } => write!(
                f,
                "{}: the node index '{}' is invalid",
                self.context,
                node.index()
            ),
            TreeErrorType::ExpectedRootNode { node } => write!(
                f,
                "{}: the node '{}' must be a root node",
                self.context,
                node.index()
            ),
            TreeErrorType::ExpectedNonAncestorNode {
                new_ancestor,
                new_descendant,
            } => write!(
                f,
                "{}: the new child node '{}' is an ancestor of the new parent node '{}'",
                self.context,
                new_ancestor.index(),
                new_descendant.index()
            ),
            TreeErrorType::OtherError { ref msg } => write!(f, "{}: {}", self.context, msg),
        }
    }
}

impl Error for TreeError {
    fn description(&self) -> &str {
        match self.error {
            TreeErrorType::InvalidNodeIndex { .. } => "Invalid node index",
            TreeErrorType::ExpectedRootNode { .. } => "Expected root node",
            TreeErrorType::ExpectedNonAncestorNode { .. } => "Expected non-ancestor node",
            TreeErrorType::OtherError { .. } => "Other error",
        }
    }

    fn cause(&self) -> Option<&dyn Error> {
        None
    }
}
