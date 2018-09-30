use prelude::*;
use rand;
use rand::Rng;
use tree::traversal::GeneralDfsValues;

#[test]
fn test_basic_tree() {
    let (tree, dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    validate(&tree);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_traversable_api() {
    let (tree, _dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let values: Vec<usize> = vec![0, 1, 5, 9, 2, 3, 4, 6, 7, 8, 10, 11, 12];
    let parents: Vec<Option<NodeIndex>> = vec![
        None,
        Some(NodeIndex(0)),
        Some(NodeIndex(0)),
        Some(NodeIndex(0)),
        Some(NodeIndex(1)),
        Some(NodeIndex(1)),
        Some(NodeIndex(1)),
        Some(NodeIndex(2)),
        Some(NodeIndex(2)),
        Some(NodeIndex(2)),
        Some(NodeIndex(3)),
        Some(NodeIndex(3)),
        Some(NodeIndex(3)),
    ];
    let children: Vec<Vec<Option<NodeIndex>>> = vec![
        vec![
            Some(NodeIndex(1)),
            Some(NodeIndex(2)),
            Some(NodeIndex(3)),
            None,
        ],
        vec![
            Some(NodeIndex(4)),
            Some(NodeIndex(5)),
            Some(NodeIndex(6)),
            None,
        ],
        vec![
            Some(NodeIndex(7)),
            Some(NodeIndex(8)),
            Some(NodeIndex(9)),
            None,
        ],
        vec![
            Some(NodeIndex(10)),
            Some(NodeIndex(11)),
            Some(NodeIndex(12)),
            None,
        ],
        vec![None, None, None, None],
        vec![None, None, None, None],
        vec![None, None, None, None],
        vec![None, None, None, None],
        vec![None, None, None, None],
        vec![None, None, None, None],
        vec![None, None, None, None],
        vec![None, None, None, None],
        vec![None, None, None, None],
    ];
    let child_counts: Vec<usize> = vec![3, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0];

    for i in 0..13 {
        assert_eq!(tree.root(NodeIndex(i)), Some(root));
        assert_eq!(tree.value(NodeIndex(i)).map(|v| *v), Some(values[i]));
        assert_eq!(tree.parent(NodeIndex(i)), parents[i]);
        assert_eq!(tree.child_count(NodeIndex(i)), child_counts[i]);
        for j in 0..4 {
            assert_eq!(tree.child(NodeIndex(i), j), children[i][j]);
        }
    }
}

#[test]
fn test_insert_child_at_first() {
    let (mut tree, mut dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    tree.insert_child_at(root, 0, 99).unwrap();
    dfs_values.insert(1, 99);
    validate(&tree);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_insert_child_at_inner() {
    let (mut tree, mut dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    tree.insert_child_at(root, 1, 99).unwrap();
    dfs_values.insert(5, 99);
    validate(&tree);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_insert_child_at_last() {
    let (mut tree, mut dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    tree.insert_child_at(root, 3, 99).unwrap();
    dfs_values.push(99);
    validate(&tree);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_insert_child_invalid() {
    let (mut tree, dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let invalid = NodeIndex(1000);
    assert!(tree.insert_child_at(invalid, 0, 99).is_err());
    validate(&tree);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_remove_root() {
    let (mut tree, dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let root1 = NodeIndex(1);
    let root2 = NodeIndex(2);
    let root3 = NodeIndex(3);
    assert_eq!(tree.remove(root).unwrap(), 0);
    validate(&tree);
    assert_eq!(
        collect_dfs_values(&tree, root1).as_slice(),
        &dfs_values[1..5]
    );
    assert_eq!(
        collect_dfs_values(&tree, root2).as_slice(),
        &dfs_values[5..9]
    );
    assert_eq!(
        collect_dfs_values(&tree, root3).as_slice(),
        &dfs_values[9..13]
    );
}

#[test]
fn test_remove_non_leaf_first() {
    let (mut tree, mut dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let removed = NodeIndex(1);
    assert_eq!(tree.remove(removed).unwrap(), 1);
    validate(&tree);
    dfs_values.remove(1);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_remove_non_leaf_inner() {
    let (mut tree, mut dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let removed = NodeIndex(2);
    assert_eq!(tree.remove(removed).unwrap(), 5);
    validate(&tree);
    dfs_values.remove(5);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_remove_non_leaf_last() {
    let (mut tree, mut dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let removed = NodeIndex(3);
    assert_eq!(tree.remove(removed).unwrap(), 9);
    validate(&tree);
    dfs_values.remove(9);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_remove_leaf_first() {
    let (mut tree, mut dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let removed = NodeIndex(4);
    assert_eq!(tree.remove(removed).unwrap(), 2);
    validate(&tree);
    dfs_values.remove(2);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_remove_leaf_inner() {
    let (mut tree, mut dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let removed = NodeIndex(5);
    assert_eq!(tree.remove(removed).unwrap(), 3);
    validate(&tree);
    dfs_values.remove(3);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_remove_leaf_last() {
    let (mut tree, mut dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let removed = NodeIndex(6);
    assert_eq!(tree.remove(removed).unwrap(), 4);
    validate(&tree);
    dfs_values.remove(4);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_remove_invalid() {
    let (mut tree, dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let removed = NodeIndex(99);
    assert!(tree.remove(removed).is_err());
    validate(&tree);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_remove_subtree_root() {
    let (mut tree, dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    assert_eq!(
        tree.remove_subtree(root)
            .unwrap()
            .iter()
            .map(|t| t.1)
            .collect::<Vec<usize>>(),
        dfs_values
    );
    validate(&tree);
}

#[test]
fn test_remove_subtree_non_leaf_first() {
    let (mut tree, _) = build_basic_tree();
    let root = NodeIndex(0);
    let removed = NodeIndex(1);
    assert_eq!(
        tree.remove_subtree(removed)
            .unwrap()
            .iter()
            .map(|t| t.1)
            .collect::<Vec<usize>>(),
        vec![1, 2, 3, 4]
    );
    validate(&tree);
    assert_eq!(
        collect_dfs_values(&tree, root),
        vec![0, 5, 6, 7, 8, 9, 10, 11, 12]
    );
}

#[test]
fn test_remove_subtree_non_leaf_inner() {
    let (mut tree, _) = build_basic_tree();
    let root = NodeIndex(0);
    let removed = NodeIndex(2);
    assert_eq!(
        tree.remove_subtree(removed)
            .unwrap()
            .iter()
            .map(|t| t.1)
            .collect::<Vec<usize>>(),
        vec![5, 6, 7, 8]
    );
    validate(&tree);
    assert_eq!(
        collect_dfs_values(&tree, root),
        vec![0, 1, 2, 3, 4, 9, 10, 11, 12]
    );
}

#[test]
fn test_remove_subtree_non_leaf_last() {
    let (mut tree, _) = build_basic_tree();
    let root = NodeIndex(0);
    let removed = NodeIndex(3);
    assert_eq!(
        tree.remove_subtree(removed)
            .unwrap()
            .iter()
            .map(|t| t.1)
            .collect::<Vec<usize>>(),
        vec![9, 10, 11, 12]
    );
    validate(&tree);
    assert_eq!(
        collect_dfs_values(&tree, root),
        vec![0, 1, 2, 3, 4, 5, 6, 7, 8]
    );
}

#[test]
fn test_remove_subtree_leaf_first() {
    let (mut tree, mut dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let removed = NodeIndex(4);
    assert_eq!(
        tree.remove_subtree(removed)
            .unwrap()
            .iter()
            .map(|t| t.1)
            .collect::<Vec<usize>>(),
        vec![2]
    );
    validate(&tree);
    dfs_values.remove(2);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_remove_subtree_leaf_inner() {
    let (mut tree, mut dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let removed = NodeIndex(5);
    assert_eq!(
        tree.remove_subtree(removed)
            .unwrap()
            .iter()
            .map(|t| t.1)
            .collect::<Vec<usize>>(),
        vec![3]
    );
    validate(&tree);
    dfs_values.remove(3);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_remove_subtree_leaf_last() {
    let (mut tree, mut dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let removed = NodeIndex(6);
    assert_eq!(
        tree.remove_subtree(removed)
            .unwrap()
            .iter()
            .map(|t| t.1)
            .collect::<Vec<usize>>(),
        vec![4]
    );
    validate(&tree);
    dfs_values.remove(4);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_remove_subtree_invalid() {
    let (mut tree, dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let removed = NodeIndex(99);
    assert!(tree.remove_subtree(removed).is_err());
    validate(&tree);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_set_as_child_non_leaf() {
    let (mut tree, mut dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let child = tree.insert(13);
    tree.insert_child(child, 14).unwrap();
    tree.insert_child(child, 15).unwrap();
    tree.insert_child(child, 16).unwrap();
    validate(&tree);
    assert!(tree.set_as_child(root, child).is_ok());
    validate(&tree);
    dfs_values.append(&mut vec![13, 14, 15, 16]);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_set_as_child_leaf() {
    let (mut tree, mut dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let leaf = NodeIndex(12);
    let child = tree.insert(13);
    tree.insert_child(child, 14).unwrap();
    tree.insert_child(child, 15).unwrap();
    tree.insert_child(child, 16).unwrap();
    validate(&tree);
    assert!(tree.set_as_child(leaf, child).is_ok());
    validate(&tree);
    dfs_values.append(&mut vec![13, 14, 15, 16]);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_set_as_child_invalid() {
    let (mut tree, dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let leaf = NodeIndex(12);
    let invalid = NodeIndex(99);
    let child = tree.insert(13);
    validate(&tree);
    assert!(tree.set_as_child(root, leaf).is_err());
    validate(&tree);
    assert!(tree.set_as_child(root, invalid).is_err());
    validate(&tree);
    assert!(tree.set_as_child(invalid, child).is_err());
    validate(&tree);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_set_as_child_at_non_leaf_first() {
    let (mut tree, mut dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let child = tree.insert(13);
    tree.insert_child(child, 14).unwrap();
    tree.insert_child(child, 15).unwrap();
    tree.insert_child(child, 16).unwrap();
    validate(&tree);
    assert!(tree.set_as_child_at(root, child, 0).is_ok());
    validate(&tree);
    dfs_values.insert(1, 16);
    dfs_values.insert(1, 15);
    dfs_values.insert(1, 14);
    dfs_values.insert(1, 13);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_set_as_child_at_non_leaf_inner() {
    let (mut tree, mut dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let child = tree.insert(13);
    tree.insert_child(child, 14).unwrap();
    tree.insert_child(child, 15).unwrap();
    tree.insert_child(child, 16).unwrap();
    validate(&tree);
    assert!(tree.set_as_child_at(root, child, 1).is_ok());
    validate(&tree);
    dfs_values.insert(5, 16);
    dfs_values.insert(5, 15);
    dfs_values.insert(5, 14);
    dfs_values.insert(5, 13);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_set_as_child_at_non_leaf_last() {
    let (mut tree, mut dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let child = tree.insert(13);
    tree.insert_child(child, 14).unwrap();
    tree.insert_child(child, 15).unwrap();
    tree.insert_child(child, 16).unwrap();
    validate(&tree);
    assert!(tree.set_as_child_at(root, child, 3).is_ok());
    validate(&tree);
    dfs_values.append(&mut vec![13, 14, 15, 16]);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_set_as_child_at_leaf() {
    let (mut tree, mut dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let leaf = NodeIndex(12);
    let child = tree.insert(13);
    tree.insert_child(child, 14).unwrap();
    tree.insert_child(child, 15).unwrap();
    tree.insert_child(child, 16).unwrap();
    validate(&tree);
    assert!(tree.set_as_child_at(leaf, child, 0).is_ok());
    validate(&tree);
    dfs_values.append(&mut vec![13, 14, 15, 16]);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_set_as_child_at_invalid() {
    let (mut tree, dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let leaf = NodeIndex(12);
    let invalid = NodeIndex(99);
    let child = tree.insert(13);
    validate(&tree);
    assert!(tree.set_as_child_at(root, leaf, 0).is_err());
    validate(&tree);
    assert!(tree.set_as_child_at(root, invalid, 0).is_err());
    validate(&tree);
    assert!(tree.set_as_child_at(invalid, child, 0).is_err());
    validate(&tree);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_remove_as_child_root() {
    let (mut tree, dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    assert!(tree.remove_as_child(root).is_ok());
    validate(&tree);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_remove_as_child_non_leaf_first() {
    let (mut tree, _) = build_basic_tree();
    let root = NodeIndex(0);
    let removed = NodeIndex(1);
    assert!(tree.remove_as_child(removed).is_ok());
    validate(&tree);
    assert_eq!(
        collect_dfs_values(&tree, root),
        vec![0, 5, 6, 7, 8, 9, 10, 11, 12]
    );
    assert_eq!(collect_dfs_values(&tree, removed), vec![1, 2, 3, 4]);
}

#[test]
fn test_remove_as_child_non_leaf_inner() {
    let (mut tree, _) = build_basic_tree();
    let root = NodeIndex(0);
    let removed = NodeIndex(2);
    assert!(tree.remove_as_child(removed).is_ok());
    validate(&tree);
    assert_eq!(
        collect_dfs_values(&tree, root),
        vec![0, 1, 2, 3, 4, 9, 10, 11, 12]
    );
    assert_eq!(collect_dfs_values(&tree, removed), vec![5, 6, 7, 8]);
}

#[test]
fn test_remove_as_child_non_leaf_last() {
    let (mut tree, _) = build_basic_tree();
    let root = NodeIndex(0);
    let removed = NodeIndex(3);
    assert!(tree.remove_as_child(removed).is_ok());
    validate(&tree);
    assert_eq!(
        collect_dfs_values(&tree, root),
        vec![0, 1, 2, 3, 4, 5, 6, 7, 8]
    );
    assert_eq!(collect_dfs_values(&tree, removed), vec![9, 10, 11, 12]);
}

#[test]
fn test_remove_as_child_leaf_first() {
    let (mut tree, mut dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let removed = NodeIndex(4);
    assert!(tree.remove_as_child(removed).is_ok());
    validate(&tree);
    dfs_values.remove(2);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
    assert_eq!(collect_dfs_values(&tree, removed), vec![2]);
}

#[test]
fn test_remove_as_child_leaf_inner() {
    let (mut tree, mut dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let removed = NodeIndex(5);
    assert!(tree.remove_as_child(removed).is_ok());
    validate(&tree);
    dfs_values.remove(3);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
    assert_eq!(collect_dfs_values(&tree, removed), vec![3]);
}

#[test]
fn test_remove_as_child_leaf_last() {
    let (mut tree, mut dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let removed = NodeIndex(6);
    assert!(tree.remove_as_child(removed).is_ok());
    validate(&tree);
    dfs_values.remove(4);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
    assert_eq!(collect_dfs_values(&tree, removed), vec![4]);
}

#[test]
fn test_remove_as_child_invalid() {
    let (mut tree, dfs_values) = build_basic_tree();
    let root = NodeIndex(0);
    let removed = NodeIndex(99);
    assert!(!tree.remove_as_child(removed).is_ok());
    validate(&tree);
    assert_eq!(collect_dfs_values(&tree, root), dfs_values);
}

#[test]
fn test_big_random_api() {
    let mut tree: Forest<usize> = Forest::new(1000);
    let mut nodes = Vec::new();
    let mut rng = rand::thread_rng();
    let mut actions = 0;

    while actions < 1000 {
        let len = nodes.len();
        if len == 0 {
            nodes.push(tree.insert(actions));
            actions += 1;
        } else {
            match rng.gen::<usize>() % 6 {
                0 => {
                    // insert
                    nodes.push(tree.insert(actions));
                    actions += 1;
                }
                1 => {
                    // insert_child
                    let idx = rng.gen::<usize>() % len;
                    let parent = nodes[idx];
                    nodes.push(tree.insert_child(parent, actions).unwrap());
                    actions += 1;
                }
                2 => {
                    // insert_child_at
                    let idx = rng.gen::<usize>() % len;
                    let parent = nodes[idx];
                    let child_count = tree.child_count(parent);
                    let pos = if child_count == 0 {
                        0
                    } else {
                        rng.gen::<usize>() % child_count
                    };
                    nodes.push(tree.insert_child_at(parent, pos, actions).unwrap());
                    actions += 1;
                }
                3 => {
                    // remove
                    let idx = rng.gen::<usize>() % len;
                    let node = nodes[idx];
                    tree.remove(node).unwrap();
                    nodes.remove(idx);
                    actions += 1;
                }
                4 => {
                    // remove_subtree
                    let idx = rng.gen::<usize>() % len;
                    let root = nodes[idx];
                    let v: Vec<NodeIndex> = tree
                        .remove_subtree(root)
                        .unwrap()
                        .iter()
                        .map(|t| t.0)
                        .collect();
                    nodes.retain(|n| !v.contains(n));
                    actions += 1;
                }
                5 => {
                    // remove_as_child
                    let idx = rng.gen::<usize>() % len;
                    let root = nodes[idx];
                    tree.remove_as_child(root).unwrap();
                    actions += 1;
                }
                _ => unreachable!(),
            }
        }
        validate(&tree);
    }
}

fn build_basic_tree() -> (Forest<usize>, Vec<usize>) {
    let mut tree: Forest<usize> = Forest::new(13);
    let n0 = tree.insert(0);
    let n1 = tree.insert_child(n0, 1).unwrap();
    let n5 = tree.insert_child(n0, 5).unwrap();
    let n9 = tree.insert_child(n0, 9).unwrap();
    tree.insert_child(n1, 2).unwrap();
    tree.insert_child(n1, 3).unwrap();
    tree.insert_child(n1, 4).unwrap();
    tree.insert_child(n5, 6).unwrap();
    tree.insert_child(n5, 7).unwrap();
    tree.insert_child(n5, 8).unwrap();
    tree.insert_child(n9, 10).unwrap();
    tree.insert_child(n9, 11).unwrap();
    tree.insert_child(n9, 12).unwrap();
    (tree, vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
}

fn collect_dfs_values(tree: &Forest<usize>, node: NodeIndex) -> Vec<usize> {
    GeneralDfsValues::new(tree, node).map(|v| *v).collect()
}

fn validate(tree: &Forest<usize>) {
    let mut root_count = 0;
    let mut child_counts = Vec::with_capacity(tree.arena.capacity());
    for _ in 0..child_counts.capacity() {
        child_counts.push(0usize);
    }
    for (index, node) in tree.arena.iter() {
        let context = (
            node.context.parent,
            node.context.prev_sibling,
            node.context.next_sibling,
        );
        match context {
            (Some(parent), Some(prev), Some(next)) => {
                assert_ne!(
                    tree.arena[parent.index()].context.first_child,
                    Some(NodeIndex(index))
                );
                assert_ne!(
                    tree.arena[parent.index()].context.last_child,
                    Some(NodeIndex(index))
                );
                assert_eq!(
                    tree.arena[prev.index()].context.next_sibling,
                    Some(NodeIndex(index))
                );
                assert_eq!(
                    tree.arena[next.index()].context.prev_sibling,
                    Some(NodeIndex(index))
                );
                child_counts[parent.index()] += 1;
            }
            (Some(parent), Some(prev), None) => {
                assert_ne!(
                    tree.arena[parent.index()].context.first_child,
                    Some(NodeIndex(index))
                );
                assert_eq!(
                    tree.arena[parent.index()].context.last_child,
                    Some(NodeIndex(index))
                );
                assert_eq!(
                    tree.arena[prev.index()].context.next_sibling,
                    Some(NodeIndex(index))
                );
                child_counts[parent.index()] += 1;
            }
            (Some(parent), None, Some(next)) => {
                assert_eq!(
                    tree.arena[parent.index()].context.first_child,
                    Some(NodeIndex(index))
                );
                assert_ne!(
                    tree.arena[parent.index()].context.last_child,
                    Some(NodeIndex(index))
                );
                assert_eq!(
                    tree.arena[next.index()].context.prev_sibling,
                    Some(NodeIndex(index))
                );
                child_counts[parent.index()] += 1;
            }
            (Some(parent), None, None) => {
                assert_eq!(
                    tree.arena[parent.index()].context.first_child,
                    Some(NodeIndex(index))
                );
                assert_eq!(
                    tree.arena[parent.index()].context.last_child,
                    Some(NodeIndex(index))
                );
                child_counts[parent.index()] += 1;
            }
            (None, Some(prev), Some(next)) => {
                assert_eq!(
                    tree.arena[prev.index()].context.next_sibling,
                    Some(NodeIndex(index))
                );
                assert_eq!(
                    tree.arena[next.index()].context.prev_sibling,
                    Some(NodeIndex(index))
                );
                assert!(tree.roots.contains(&NodeIndex(index)));
                root_count += 1;
            }
            (None, Some(prev), None) => {
                assert_eq!(
                    tree.arena[prev.index()].context.next_sibling,
                    Some(NodeIndex(index))
                );
                assert!(tree.roots.contains(&NodeIndex(index)));
                root_count += 1;
            }
            (None, None, Some(next)) => {
                assert_eq!(
                    tree.arena[next.index()].context.prev_sibling,
                    Some(NodeIndex(index))
                );
                assert!(tree.roots.contains(&NodeIndex(index)));
                root_count += 1;
            }
            (None, None, None) => {
                assert!(tree.roots.contains(&NodeIndex(index)));
                root_count += 1;
            }
        }
        assert_eq!(tree.children(NodeIndex(index)).count(), node.child_count);
    }
    for (index, count) in child_counts.iter().enumerate() {
        assert_eq!(tree.arena.get(index).map_or(0, |v| v.child_count), *count);
    }
    assert_eq!(root_count, tree.roots.len());
}
