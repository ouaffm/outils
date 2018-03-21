use prelude::*;
use rand;
use rand::Rng;
use std::cmp::Ordering;
use super::WeightedAaForest;
use tree::Tgf;

#[test]
fn test_api() {
    let mut tree: WeightedAaForest<i64> = WeightedAaForest::new(6);
    let n0 = tree.insert(0);
    let n1 = tree.insert(1);
    let n2 = tree.insert(2);
    let n3 = tree.insert(3);
    assert!(tree.remove(n2) == Some(2));

    let nodes = vec![n2, NodeIndex(0), NodeIndex(10)];

    for node in nodes {
        assert!(tree.root(node).is_none());
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
        assert!(!tree.is_smaller(n1, node));
        assert!(!tree.is_smaller(node, n1));
    }
}

#[test]
fn test_basic_append_ascending() {
    let mut tree: WeightedAaForest<i64> = WeightedAaForest::new(6);
    let n0 = tree.insert(0);
    let n1 = tree.insert(1);
    let n2 = tree.insert(2);
    let n3 = tree.insert(3);
    let n4 = tree.insert(4);
    let n5 = tree.insert(5);
    let n6 = tree.insert(6);

    let mut rt = tree.append(n0, n1).unwrap();
    rt = tree.append(rt, n2).unwrap();
    rt = tree.append(rt, n3).unwrap();
    rt = tree.append(rt, n4).unwrap();
    rt = tree.append(rt, n5).unwrap();
    tree.append(rt, n6);

    assert!(is_binary_search_forest(
        &mut tree,
        i64::min_value(),
        i64::max_value()
    ));
    assert!(is_aa_forest(&mut tree));
}

#[test]
fn test_basic_append_descending() {
    let mut tree: WeightedAaForest<i64> = WeightedAaForest::new(6);
    let n0 = tree.insert(6);
    let n1 = tree.insert(5);
    let n2 = tree.insert(4);
    let n3 = tree.insert(3);
    let n4 = tree.insert(2);
    let n5 = tree.insert(1);
    let n6 = tree.insert(0);

    let mut rt = tree.append(n1, n0).unwrap();
    rt = tree.append(n2, rt).unwrap();
    rt = tree.append(n3, rt).unwrap();
    rt = tree.append(n4, rt).unwrap();
    rt = tree.append(n5, rt).unwrap();
    tree.append(n6, rt);

    assert!(is_binary_search_forest(
        &mut tree,
        i64::min_value(),
        i64::max_value()
    ));
    assert!(is_aa_forest(&mut tree));
}

#[test]
fn test_bulk_append() {
    let mut tree: WeightedAaForest<i64> = WeightedAaForest::new(30);
    let mut rt1 = tree.insert(1);
    let mut rt2 = tree.insert(21);
    let mut rt3 = tree.insert(31);
    let mut rt4 = tree.insert(41);

    for x in 2..20 {
        let node = tree.insert(x);
        tree.set_weight(node, x as usize);
        rt1 = tree.append(rt1, node).unwrap();
    }

    assert!(is_binary_search_forest(
        &mut tree,
        i64::min_value(),
        i64::max_value()
    ));
    assert!(is_aa_forest(&mut tree));
    assert!(is_weighted_binary_forest(&mut tree));

    for x in 22..30 {
        let node = tree.insert(x);
        tree.set_weight(node, x as usize);
        rt2 = tree.append(rt2, node).unwrap();
    }

    assert!(is_binary_search_forest(
        &mut tree,
        i64::min_value(),
        i64::max_value()
    ));
    assert!(is_aa_forest(&mut tree));
    assert!(is_weighted_binary_forest(&mut tree));

    for x in 32..40 {
        let node = tree.insert(x);
        tree.set_weight(node, x as usize);
        rt3 = tree.append(rt3, node).unwrap();
    }

    assert!(is_binary_search_forest(
        &mut tree,
        i64::min_value(),
        i64::max_value()
    ));
    assert!(is_aa_forest(&mut tree));
    assert!(is_weighted_binary_forest(&mut tree));

    for x in 42..70 {
        let node = tree.insert(x);
        tree.set_weight(node, x as usize);
        rt4 = tree.append(rt4, node).unwrap();
    }

    assert!(is_binary_search_forest(
        &mut tree,
        i64::min_value(),
        i64::max_value()
    ));
    assert!(is_aa_forest(&mut tree));
    assert!(is_weighted_binary_forest(&mut tree));

    rt1 = tree.append(rt1, rt2).unwrap();
    assert!(is_binary_search_forest(
        &mut tree,
        i64::min_value(),
        i64::max_value()
    ));
    assert!(is_aa_forest(&mut tree));
    assert!(is_weighted_binary_forest(&mut tree));

    rt3 = tree.append(rt3, rt4).unwrap();
    assert!(is_binary_search_forest(
        &mut tree,
        i64::min_value(),
        i64::max_value()
    ));
    assert!(is_aa_forest(&mut tree));
    assert!(is_weighted_binary_forest(&mut tree));

    tree.append(rt1, rt3).unwrap();
    assert!(is_binary_search_forest(
        &mut tree,
        i64::min_value(),
        i64::max_value()
    ));
    assert!(is_aa_forest(&mut tree));
    assert!(is_weighted_binary_forest(&mut tree));
}

#[test]
fn test_basic_split() {
    let mut tree: WeightedAaForest<i64> = WeightedAaForest::new(6);
    let n0 = tree.insert(0);
    let n1 = tree.insert(1);
    let n2 = tree.insert(2);
    let n3 = tree.insert(3);
    let n4 = tree.insert(4);
    let n5 = tree.insert(5);
    let n6 = tree.insert(6);

    let mut rt = tree.append(n0, n1).unwrap();
    rt = tree.append(rt, n2).unwrap();
    rt = tree.append(rt, n3).unwrap();
    rt = tree.append(rt, n4).unwrap();
    rt = tree.append(rt, n5).unwrap();
    tree.append(rt, n6);

    tree.split(n5, BstDirection::Right);
    tree.split(n3, BstDirection::Left);

    assert!(is_binary_search_forest(
        &mut tree,
        i64::min_value(),
        i64::max_value()
    ));
    assert!(is_aa_forest(&mut tree));
}

#[test]
fn test_split_middle() {
    let mut tree: WeightedAaForest<i64> = WeightedAaForest::new(13);
    let values = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];
    let mut nodes = Vec::new();
    for v in values {
        nodes.push(tree.insert(v));
    }
    let mut rt = nodes[0];
    for i in 1..nodes.len() {
        rt = tree.append(rt, nodes[i]).unwrap();
        assert!(is_aa_forest(&mut tree));
    }

    tree.split(nodes[3], BstDirection::Right);
    assert!(is_aa_forest(&mut tree));
}

#[test]
fn test_big_tree_append_and_split() {
    let mut tree: WeightedAaForest<i64> = WeightedAaForest::new(100);
    let mut list = Vec::with_capacity(100);
    let mut rt = tree.insert(0);

    list.push(rt);
    for x in 1..100 {
        let node = tree.insert(x);
        tree.set_weight(node, x as usize);
        list.push(node);
        rt = tree.append(rt, node).unwrap();
        assert!(is_binary_search_forest(
            &mut tree,
            i64::min_value(),
            i64::max_value()
        ));
        assert!(is_aa_forest(&mut tree));
        assert!(is_weighted_binary_forest(&mut tree));
    }

    for x in list {
        tree.split(x, BstDirection::Left);
        assert!(is_binary_search_forest(
            &mut tree,
            i64::min_value(),
            i64::max_value()
        ));
        assert!(is_aa_forest(&mut tree));
        assert!(is_weighted_binary_forest(&mut tree));
    }
}

#[test]
fn test_big_tree_append_and_split_all() {
    let mut tree: WeightedAaForest<i64> = WeightedAaForest::new(100);
    let mut list = Vec::with_capacity(100);
    let mut rt = tree.insert(0);

    list.push(rt);
    for x in 1..100 {
        let node = tree.insert(x);
        tree.set_weight(node, x as usize);
        list.push(node);
        rt = tree.append(rt, node).unwrap();
        assert!(is_binary_search_forest(
            &mut tree,
            i64::min_value(),
            i64::max_value()
        ));
        assert!(is_aa_forest(&mut tree));
        assert!(is_weighted_binary_forest(&mut tree));
    }
    tree.split_all(rt, None);
    assert!(is_aa_forest(&mut tree));
    assert!(is_weighted_binary_forest(&mut tree));
}

#[test]
fn test_big_random_tree_append_and_delete() {
    let mut tree: WeightedAaForest<i64> = WeightedAaForest::new(1000);
    let mut list = Vec::with_capacity(1000);
    let mut rt = tree.insert(0);
    list.push(rt);
    for x in 1..999 {
        let node = tree.insert(x);
        list.push(node);
        rt = tree.append(rt, node).unwrap();
    }

    assert!(is_binary_search_forest(
        &mut tree,
        i64::min_value(),
        i64::max_value()
    ));
    assert!(is_aa_forest(&mut tree));

    let mut rng = rand::thread_rng();
    let mut stop = false;
    while stop == false {
        stop = true;
        for x in 0..list.len() {
            let node = list[x];
            if node.index() != 0 {
                stop = false;
            }
            if rng.gen::<i64>() > 0 {
                tree.remove(node);
                assert!(is_binary_search_forest(
                    &mut tree,
                    i64::min_value(),
                    i64::max_value()
                ));
                assert!(is_aa_forest(&mut tree));
                list[x] = NodeIndex(0);
            }
        }
    }
}

#[test]
fn test_big_random_tree_append_and_split() {
    let mut tree: WeightedAaForest<i64> = WeightedAaForest::new(1000);
    let mut list = Vec::with_capacity(1000);
    let mut rt = tree.insert(0);
    list.push(rt);
    for x in 1..999 {
        let node = tree.insert(x);
        tree.set_weight(node, x as usize);
        list.push(node);
        rt = tree.append(rt, node).unwrap();
    }
    assert!(is_binary_search_forest(
        &mut tree,
        i64::min_value(),
        i64::max_value()
    ));
    assert!(is_aa_forest(&mut tree));
    assert!(is_weighted_binary_forest(&mut tree));

    let mut rng = rand::thread_rng();
    let mut stop = false;
    while stop == false {
        stop = true;
        for x in 0..list.len() {
            let node = list[x];
            if node.index() != 0 {
                stop = false;
            }
            if rng.gen::<i64>() > 0 {
                let dir = if rng.gen::<i64>() > 0 {
                    BstDirection::Left
                } else {
                    BstDirection::Right
                };
                tree.split(node, dir);
                assert!(is_binary_search_forest(
                    &mut tree,
                    i64::min_value(),
                    i64::max_value()
                ));
                assert!(is_aa_forest(&mut tree));
                assert!(is_weighted_binary_forest(&mut tree));
                list[x] = NodeIndex(0);
            }
        }
    }
}

#[test]
fn test_big_tree_append_and_delete() {
    let mut tree: WeightedAaForest<i64> = WeightedAaForest::new(1000);
    let mut list = Vec::with_capacity(1000);
    let mut rt = tree.insert(0);

    list.push(rt);
    for x in 1..1000 {
        let node = tree.insert(x);
        tree.set_weight(node, x as usize);
        list.push(node);
        rt = tree.append(rt, node).unwrap();

        assert!(is_binary_search_forest(
            &mut tree,
            i64::min_value(),
            i64::max_value()
        ));
        assert!(is_aa_forest(&mut tree));
        assert!(is_weighted_binary_forest(&mut tree));
    }

    for x in list {
        tree.remove(x);
        assert!(is_binary_search_forest(
            &mut tree,
            i64::min_value(),
            i64::max_value()
        ));
        assert!(is_aa_forest(&mut tree));
        assert!(is_weighted_binary_forest(&mut tree));
    }
}

#[test]
fn test_big_tree_is_smaller() {
    let mut tree: WeightedAaForest<i64> = WeightedAaForest::new(100);
    let mut list = Vec::with_capacity(100);
    let mut rt = tree.insert(0);

    list.push(rt);
    for x in 1..100 {
        let node = tree.insert(x);
        list.push(node);
        rt = tree.append(rt, node).unwrap();

        assert!(is_binary_search_forest(
            &mut tree,
            i64::min_value(),
            i64::max_value()
        ));
        assert!(is_aa_forest(&mut tree));
    }
    for x in 1..100 {
        for y in 1..100 {
            let val_x = tree.arena[list[x].index()].value;
            let val_y = tree.arena[list[y].index()].value;
            assert!((val_x < val_y) == tree.is_smaller(list[x], list[y]));
            assert!((val_y < val_x) == tree.is_smaller(list[y], list[x]));
        }
    }
}

fn is_weighted_binary_forest(tree: &mut WeightedAaForest<i64>) -> bool {
    let iter = tree.arena.iter();

    for (index, node) in iter {
        if node.parent == tree.nil {
            if is_weighted_binary_tree(tree, index) == false {
                return false;
            }
        }
    }
    true
}

fn is_weighted_binary_tree(tree: &WeightedAaForest<i64>, node: usize) -> bool {
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

fn is_binary_search_forest(tree: &mut WeightedAaForest<i64>, min: i64, max: i64) -> bool {
    let iter = tree.arena.iter();

    for (index, node) in iter {
        if node.parent == tree.nil {
            if is_binary_search_tree(tree, index, min, max) == false {
                return false;
            }
        }
    }
    true
}

fn is_binary_search_tree(tree: &WeightedAaForest<i64>, node: usize, min: i64, max: i64) -> bool {
    if node == tree.nil {
        return true;
    }
    let value = tree.arena[node].value;
    let min_ok = min.cmp(&value) != Ordering::Greater;
    let max_ok = max.cmp(&value) != Ordering::Less;

    if min_ok && max_ok == false {
        let tgf = tree.to_tgf();
        println!("NoBinarySearchTree1 ({}):\n\n{}", node, tgf);
        return false;
    }

    let left = tree.arena[node][BstDirection::Left];
    let right = tree.arena[node][BstDirection::Right];

    if left != tree.nil && tree.arena[left].parent != node {
        let tgf = tree.to_tgf();
        println!("NoBinarySearchTree2 ({}):\n\n{}", left, tgf);
        return false;
    }

    if right != tree.nil && tree.arena[right].parent != node {
        let tgf = tree.to_tgf();
        println!("NoBinarySearchTree3 ({}):\n\n{}", right, tgf);
        return false;
    }

    is_binary_search_tree(tree, left, min, value - 1)
        && is_binary_search_tree(tree, right, value + 1, max)
}

fn is_aa_forest(tree: &mut WeightedAaForest<i64>) -> bool {
    let iter = tree.arena.iter();

    for (index, node) in iter {
        if node.parent == tree.nil {
            if is_aa_tree(tree, index) == false {
                return false;
            }
        }
    }
    true
}

fn is_aa_tree(tree: &WeightedAaForest<i64>, node: usize) -> bool {
    if node <= tree.sdummy {
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
