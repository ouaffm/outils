use prelude::*;
use rand;
use rand::Rng;
use std::cmp::Ordering;
use super::WeightedAaTree;
use types::Tgf;

#[test]
fn test_api() {
    let mut tree: WeightedAaTree<i64, &str> = WeightedAaTree::new(6);
    tree.insert(0, "0");
    tree.insert(1, "1");
    tree.insert(2, "2");
    tree.insert(3, "3");
    assert!(tree.remove(&2).is_some());

    let nodes = vec![NodeIndex(5), NodeIndex(0), NodeIndex(10)];

    for node in nodes {
        assert!(tree.value(node).is_none());
        assert!(tree.value_mut(node).is_none());
        assert!(tree.parent(node).is_none());
        assert!(tree.child(node, 0).is_none());
        assert!(tree.child_count(node) == 0);
        assert!(tree.sub_predecessor(node).is_none());
        assert!(tree.sub_successor(node).is_none());
        assert!(tree.predecessor(node).is_none());
        assert!(tree.successor(node).is_none());
        assert!(tree.first(node).is_none());
        assert!(tree.last(node).is_none());
        assert!(!tree.is_smaller(NodeIndex(4), node));
        assert!(!tree.is_smaller(node, NodeIndex(4)));
    }
}

#[test]
fn test_basic_insert_ascending() {
    let mut tree: WeightedAaTree<i64, &str> = WeightedAaTree::new(6);
    tree.insert(0, "0");
    tree.insert(1, "1");
    tree.insert(2, "2");
    tree.insert(3, "3");
    tree.insert(4, "4");
    tree.insert(5, "5");
    tree.insert(6, "6");

    let rt = tree.root;
    assert!(check_edge_count(&tree));
    assert!(is_binary_search_tree(
        &mut tree,
        rt,
        i64::min_value(),
        i64::max_value()
    ));
    assert!(is_aa_tree(&mut tree, rt));
}

#[test]
fn test_basic_insert_descending() {
    let mut tree: WeightedAaTree<i64, &str> = WeightedAaTree::new(6);
    tree.insert(6, "6");
    tree.insert(5, "5");
    tree.insert(4, "4");
    tree.insert(3, "3");
    tree.insert(2, "2");
    let rt = tree.root;
    assert!(check_edge_count(&tree));
    assert!(is_binary_search_tree(
        &mut tree,
        rt,
        i64::min_value(),
        i64::max_value()
    ));
    assert!(is_aa_tree(&mut tree, rt));
}

#[test]
fn test_basic_delete() {
    let mut tree: WeightedAaTree<i64, &str> = WeightedAaTree::new(6);
    tree.insert(0, "0");
    tree.insert(1, "1");
    tree.insert(2, "2");
    tree.insert(3, "3");
    tree.insert(4, "4");
    tree.insert(5, "5");
    tree.insert(6, "6");
    tree.remove(&3);

    assert!(tree.remove(&10).is_none());

    let rt = tree.root;
    assert!(check_edge_count(&tree));
    assert!(is_binary_search_tree(
        &mut tree,
        rt,
        i64::min_value(),
        i64::max_value()
    ));
    assert!(is_aa_tree(&mut tree, rt));
}

#[test]
fn test_big_tree_insert_and_delete() {
    let mut tree: WeightedAaTree<i64, &str> = WeightedAaTree::new(100);
    let mut list: Vec<i64> = Vec::with_capacity(100);

    for x in 0..50 {
        list.push(x);
        let y = 50 + x;
        list.push(y);
        tree.insert_weighted(x, "", x as usize);
        tree.insert_weighted(y, "", y as usize);
    }

    let rt = tree.root;
    assert!(check_edge_count(&tree));
    assert!(is_binary_search_tree(
        &mut tree,
        rt,
        i64::min_value(),
        i64::max_value()
    ));
    assert!(is_aa_tree(&mut tree, rt));
    assert!(is_weighted_binary_tree(&mut tree, rt));

    for x in list {
        assert!(tree.remove(&x).is_some());
        let rt = tree.root;
        assert!(check_edge_count(&tree));
        assert!(is_binary_search_tree(
            &mut tree,
            rt,
            i64::min_value(),
            i64::max_value()
        ));
        assert!(is_aa_tree(&mut tree, rt));
        assert!(is_weighted_binary_tree(&mut tree, rt));
    }
}

#[test]
fn test_big_random_tree_insert_and_delete() {
    let mut tree: WeightedAaTree<i64, &str> = WeightedAaTree::new(1000);
    let mut list: Vec<i64> = Vec::with_capacity(1000);
    let mut rng = rand::thread_rng();
    for x in 0..1000 {
        let y = rng.gen::<i64>();
        list.push(y);
        tree.insert_weighted(y, "", x as usize);
    }

    let rt = tree.root;
    assert!(is_binary_search_tree(
        &mut tree,
        rt,
        i64::min_value(),
        i64::max_value()
    ));
    assert!(is_aa_tree(&mut tree, rt));
    assert!(is_weighted_binary_tree(&mut tree, rt));

    for x in list {
        assert!(tree.remove(&x).is_some());

        let rt = tree.root;
        assert!(is_binary_search_tree(
            &mut tree,
            rt,
            i64::min_value(),
            i64::max_value()
        ));
        assert!(is_aa_tree(&mut tree, rt));
        assert!(is_weighted_binary_tree(&mut tree, rt));
    }
}

fn check_edge_count(tree: &WeightedAaTree<i64, &str>) -> bool {
    let node_count = tree.arena.len();
    let mut edge_count = 0;
    let mut parent_count = 0;
    let iter = tree.arena.iter();
    for (_, node) in iter {
        if node.parent != tree.nil {
            parent_count += 1;
        }
        if node[BstDirection::Left] != tree.nil {
            edge_count += 1;
        }
        if node[BstDirection::Right] != tree.nil {
            edge_count += 1;
        }
    }
    if node_count == 1 {
        return edge_count == 0 && parent_count == 0;
    }

    return node_count == edge_count + 2 && node_count == parent_count + 2;
}

fn is_weighted_binary_tree(tree: &WeightedAaTree<i64, &str>, node: usize) -> bool {
    if node == tree.nil {
        return true;
    }
    let left = tree.arena[node][BstDirection::Left];
    let right = tree.arena[node][BstDirection::Right];

    let node_weight = tree.arena[node].weight;
    let node_subweight = tree.arena[node].subweight;
    let left_subweight = tree.arena[left].subweight;
    let right_subweight = tree.arena[right].subweight;

    if node_subweight != node_weight + left_subweight + right_subweight {
        let tgf = tree.to_tgf();
        println!("NoWeightedBinaryTree ({}):\n\n{}", node, tgf);
        return false;
    }

    is_weighted_binary_tree(tree, left) && is_weighted_binary_tree(tree, right)
}

fn is_binary_search_tree(
    tree: &mut WeightedAaTree<i64, &str>,
    node: usize,
    min: i64,
    max: i64,
) -> bool {
    if node == tree.nil {
        return true;
    }

    let min_ok = tree.compare(&min, node)
        .map(|x| x != Ordering::Greater)
        .unwrap_or(false);
    let max_ok = tree.compare(&max, node)
        .map(|x| x != Ordering::Less)
        .unwrap_or(false);

    if min_ok && max_ok == false {
        let tgf = tree.to_tgf();
        println!("NoBinarySearchTree ({}):\n\n{}", node, tgf);
        return false;
    }

    let key = tree.arena[node].key;

    let left = tree.arena[node][BstDirection::Left];
    let right = tree.arena[node][BstDirection::Right];

    is_binary_search_tree(tree, left, min, key - 1)
        && is_binary_search_tree(tree, right, key + 1, max)
}

fn is_aa_tree(tree: &mut WeightedAaTree<i64, &str>, node: usize) -> bool {
    if node == tree.nil {
        return true;
    }

    let node_level = tree.arena[node].level;
    let left = tree.arena[node][BstDirection::Left];
    let left_level = tree.arena[left].level;
    let right = tree.arena[node][BstDirection::Right];
    let right_level = tree.arena[right].level;

    if left_level == 0 && right_level == 0 && node_level != 1 {
        let tgf = tree.to_tgf();
        println!("AAInvariant1Violated ({}):\n\n{}", node, tgf);
        return false;
    }

    if left_level != 0 && node_level != left_level + 1 {
        let tgf = tree.to_tgf();
        println!("AAInvariant2Violated ({}):\n\n{}", node, tgf);
        return false;
    }

    let dif = node_level - right_level;
    if right_level != 0 && dif != 0 && dif != 1 {
        let tgf = tree.to_tgf();
        println!("AAInvariant3Violated ({}):\n\n{}", node, tgf);
        return false;
    }

    let right_right = tree.arena[right][BstDirection::Right];
    let right_right_level = tree.arena[right_right].level;

    if right_level != 0 && node_level - right_right_level <= 0 {
        let tgf = tree.to_tgf();
        println!("AAInvariant4Violated ({}):\n\n{}", node, tgf);
        return false;
    }

    if node_level > 1 && (left_level == 0 || right_level == 0) {
        let tgf = tree.to_tgf();
        println!("AAInvariant5Violated ({}):\n\n{}", node, tgf);
        return false;
    }

    is_aa_tree(tree, left) && is_aa_tree(tree, right)
}
