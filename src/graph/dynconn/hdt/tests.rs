//use graph::dynconn::{DynamicComponent, DynamicConnectivity};
use prelude::*;
use rand;
use rand::Rng;
use std::mem::{size_of, size_of_val};
use super::{EdgeDirection, EdgeIndex, EulerVertex, VertexWeight};
use tree::traversal::BinaryInOrder;

//use tree::WeightedTree;
//use types::{NodeIndex, VertexIndex};

#[test]
fn test_basic_insert() {
    let mut dyn: DynamicGraph<usize> = DynamicGraph::new(5, 3);
    let _e1 = dyn.insert_edge(VertexIndex(0), VertexIndex(1));
    let _e2 = dyn.insert_edge(VertexIndex(1), VertexIndex(2));
    let _e3 = dyn.insert_edge(VertexIndex(3), VertexIndex(4));
    let _e4 = dyn.insert_edge(VertexIndex(1), VertexIndex(3));
    let _e5 = dyn.insert_edge(VertexIndex(2), VertexIndex(4));
    let e6 = dyn.insert_edge(VertexIndex(0), VertexIndex(3));
    let _e7 = dyn.insert_edge(VertexIndex(3), VertexIndex(1));
    dyn.delete_edge(e6.unwrap());
    assert!(validate(&dyn));
    assert!(dyn.is_connected(VertexIndex(0), VertexIndex(4)));
}

#[test]
fn test_big_insert_and_delete() {
    let mut dyn: DynamicGraph<usize> = DynamicGraph::new(50, 3);
    let mut edges = Vec::new();
    for i in 0..9 {
        edges.push(dyn.insert_edge(VertexIndex(i), VertexIndex(i + 1)).unwrap());
        assert!(validate(&dyn));
    }
    for i in 11..19 {
        edges.push(dyn.insert_edge(VertexIndex(i), VertexIndex(i + 1)).unwrap());
        assert!(validate(&dyn));
    }
    for i in 21..29 {
        edges.push(dyn.insert_edge(VertexIndex(i), VertexIndex(i + 1)).unwrap());
        assert!(validate(&dyn));
    }
    for i in 31..39 {
        edges.push(dyn.insert_edge(VertexIndex(i), VertexIndex(i + 1)).unwrap());
        assert!(validate(&dyn));
    }
    edges.push(dyn.insert_edge(VertexIndex(4), VertexIndex(14)).unwrap());
    assert!(validate(&dyn));
    edges.push(dyn.insert_edge(VertexIndex(15), VertexIndex(25)).unwrap());
    assert!(validate(&dyn));
    edges.push(dyn.insert_edge(VertexIndex(26), VertexIndex(36)).unwrap());
    assert!(validate(&dyn));

    for e in edges.iter() {
        dyn.delete_edge(*e);
        assert!(validate(&dyn));
    }
}

#[test]
fn test_big_insert_and_disconnect() {
    let mut dyn: DynamicGraph<usize> = DynamicGraph::new(50, 3);
    let mut edges = Vec::new();
    for i in 0..9 {
        dyn.insert_edge(VertexIndex(i), VertexIndex(i + 1)).unwrap();
        assert!(validate(&dyn));
    }
    for i in 1..4 {
        dyn.insert_edge(VertexIndex(i), VertexIndex(i * 2)).unwrap();
        assert!(validate(&dyn));
    }
    for i in 11..19 {
        dyn.insert_edge(VertexIndex(i), VertexIndex(i + 1)).unwrap();
        assert!(validate(&dyn));
    }
    for i in 1..4 {
        dyn.insert_edge(VertexIndex(i + 10), VertexIndex((i * 2) + 10))
            .unwrap();
        assert!(validate(&dyn));
    }
    for i in 21..29 {
        dyn.insert_edge(VertexIndex(i), VertexIndex(i + 1)).unwrap();
        assert!(validate(&dyn));
    }
    for i in 1..4 {
        edges.push(
            dyn.insert_edge(VertexIndex(i + 20), VertexIndex((i * 2) + 20))
                .unwrap(),
        );
        assert!(validate(&dyn));
    }
    for i in 31..39 {
        dyn.insert_edge(VertexIndex(i), VertexIndex(i + 1)).unwrap();
        assert!(validate(&dyn));
    }
    for i in 1..4 {
        dyn.insert_edge(VertexIndex(i + 30), VertexIndex((i * 2) + 30))
            .unwrap();
        assert!(validate(&dyn));
    }
    dyn.disconnect_component(VertexIndex(4));
    assert!(validate(&dyn));
    dyn.disconnect_component(VertexIndex(15));
    assert!(validate(&dyn));
    dyn.disconnect_component(VertexIndex(26));
    assert!(validate(&dyn));
    dyn.disconnect_component(VertexIndex(37));
    assert!(validate(&dyn));

    assert!(dyn.edges.edges.len() == 0);
    assert!(dyn.ext_euler.forest.node_count() == 50);
    for i in 0..dyn.max_level + 1 {
        assert!(dyn.euler[i].forest.node_count() == 50);
    }
}

#[test]
fn test_big_random_insert_and_delete() {
    let mut dyn: DynamicGraph<usize> = DynamicGraph::new(20, 10);
    let mut edges = Vec::new();
    let mut rng = rand::thread_rng();
    for _ in 0..100 {
        for _ in 0..10 {
            let src = VertexIndex(rng.gen::<usize>() % 20);
            let dst = VertexIndex(rng.gen::<usize>() % 20);
            let e = dyn.insert_edge(src, dst);
            e.map(|edge| {
                edges.push(edge);
                assert!(validate(&dyn));
            });
        }
        for _ in 0..5 {
            let e = rng.gen::<usize>() % edges.len();
            dyn.delete_edge(edges[e]);
            edges.remove(e);
        }
    }
    for e in edges.iter() {
        dyn.delete_edge(*e);
        assert!(validate(&dyn));
    }
}

#[test]
fn test_complete_insert_delete() {
    let mut dyn: DynamicGraph<usize> = DynamicGraph::new(100, 100);
    let mut edges = Vec::with_capacity(10000);

    for i in 0..100 {
        for j in 0..100 {
            dyn.insert_edge(VertexIndex(i), VertexIndex(j))
                .map(|e| edges.push(e));
        }
    }
    for e in edges.iter() {
        dyn.delete_edge(*e);
    }
    assert!(validate(&dyn));
}

fn validate(dyn: &DynamicGraph<usize>) -> bool {
    let components: Vec<VertexIndex> = dyn.components().collect();
    let mut n_components = 0;
    for level in 0..dyn.max_level {
        for i in 0..dyn.euler[level].vertices.vertices.len() {
            let n = dyn.euler[level].vertices.vertices[i].active_node;
            if dyn.euler[level].forest.weight(n).map_or(0, |w| w.act_count) != 1 {
                println!(
                    "{:?} ({:?}) should be active at level {:?}",
                    VertexIndex(i),
                    n,
                    level
                );
                return false;
            }
            if level == 0 {
                let edge_count_check = dyn
                    .component_vertices(VertexIndex(i))
                    .flat_map(move |v| dyn.edges.edges.iter().filter(move |e| e.1.src == v))
                    .count();
                let edge_count = dyn.component_edges(VertexIndex(i)).count();
                if edge_count != edge_count_check {
                    println!(
                        "{:?} with edge_count {:?} has incorrect number of component edges: {:?}",
                        VertexIndex(i),
                        edge_count_check,
                        edge_count,
                    );
                    return false;
                }
            }
        }
        for i in 3..((dyn.euler[level].vertices.vertices.len() * 2) + 3) {
            assert!(
                dyn.ext_euler.forest.value(NodeIndex(i)).is_none()
                    || size_of_val(
                    &dyn.ext_euler
                        .forest
                        .weight(NodeIndex(i))
                        .map_or(VertexWeight::default(), |w| *w)
                ) == 3 * size_of::<usize>()
            );
            assert!(
                dyn.euler[level].forest.value(NodeIndex(i)).is_none()
                    || size_of_val(
                    &dyn.euler[level]
                        .forest
                        .weight(NodeIndex(i))
                        .map_or(VertexWeight::default(), |w| *w)
                ) == 2 * size_of::<usize>()
            );
            if dyn.euler[level].forest.value(NodeIndex(i)).is_none() {
                continue;
            }
            if dyn.euler[level]
                .forest
                .weight(NodeIndex(i))
                .map_or(0, |w| w.act_count)
                != 0
                {
                if dyn.euler[level].vertices[dyn.euler[level].forest[NodeIndex(i)].vertex]
                    .active_node
                    != NodeIndex(i)
                {
                    println!("{:?} should be active at level {:?}", NodeIndex(i), level);
                    return false;
                }
            }
            if dyn.euler[level].forest.parent(NodeIndex(i)).is_none() {
                if level == 0 {
                    let vertex = dyn.euler[0].forest[NodeIndex(i)].vertex;
                    n_components += 1;
                    if !components.contains(&vertex) {
                        println!(
                            "Component root {:?} not contained in component list",
                            vertex
                        );
                        return false;
                    }
                }
                if validate_component(dyn, level, NodeIndex(i)) == false {
                    return false;
                }
            }
        }
    }
    if n_components != components.len() {
        println!(
            "Found {:?} component roots, expected {:?}, {:?}",
            n_components,
            components.len(),
            components
        );
        return false;
    }
    for item in dyn.edges.edges.iter() {
        let idx = EdgeIndex(item.0);
        let e = *(item.1);
        if e.is_tree_edge == true {
            if dyn.ext_euler.is_connected(e.src, e.dst) == false {
                println!("Tree {:?} not connected in external forest", e);
                return false;
            }
            for i in 0..(dyn.max_level + 1) {
                if i <= e.level {
                    if dyn.euler[i].is_connected(e.src, e.dst) == false {
                        println!("Tree {:?} not connected at level {:?}", e, i);
                        return false;
                    }
                } else {
                    if dyn.euler[i].is_connected(e.src, e.dst) == true {
                        println!("Tree {:?} connected at level {:?}", e, i);
                        return false;
                    }
                }
            }
        } else {
            if dyn.ext_euler.is_connected(e.src, e.dst) == false {
                println!("Non tree {:?} not connected in external forest", e);
                return false;
            }
            if dyn.is_connected(e.src, e.dst) == false {
                println!("is_connected() == false for non tree {:?}", e);
                return false;
            } else {
                for i in 0..(dyn.max_level + 1) {
                    if i == e.level {
                        if dyn.euler[i].adjacent_edge_index(e.src, idx).is_none() {
                            println!(
                                "Non tree {:?} not found in adj_edges[{:?}][{:?}]",
                                e, i, e.src
                            );
                            return false;
                        }
                        if dyn.euler[i].adjacent_edge_index(e.dst, idx).is_none() {
                            println!(
                                "Non tree {:?} not found in adj_edges[{:?}][{:?}]",
                                e, i, e.dst
                            );
                            return false;
                        }
                    } else {
                        if dyn.euler[i].adjacent_edge_index(e.src, idx).is_some() {
                            println!("Non tree {:?} found in adj_edges[{:?}][{:?}]", e, i, e.src);
                            return false;
                        }
                        if dyn.euler[i].adjacent_edge_index(e.dst, idx).is_some() {
                            println!(
                                "Non tree {:?} found in adj_edges[{:?}][{:?}]",
                                idx, i, e.dst
                            );
                            return false;
                        }
                    }
                }
            }
        }
    }
    true
}

fn validate_component(dyn: &DynamicGraph<usize>, level: usize, n: NodeIndex) -> bool {
    let max_size = ((dyn.size as f64) / (2.0_f64).powi(level as i32)).floor() as usize;
    let act_size = dyn.euler[level]
        .forest
        .subweight(n)
        .map_or(0, |w| w.act_count);
    if act_size > max_size {
        println!(
            "Component size of {:?} at level {:?} = {:?} > max = {:?}",
            dyn.euler[level].forest[n], level, act_size, max_size
        );
        return false;
    }

    let seq = euler_sequence(dyn, level, n);
    if seq.len() == 1 {
        return validate_singleton(dyn, level, seq[0]);
    } else {
        if validate_first(dyn, level, &seq) == false {
            return false;
        }
        for i in 1..seq.len() - 1 {
            if validate_inner(dyn, level, i, &seq) == false {
                return false;
            }
        }
        if validate_last(dyn, level, &seq) == false {
            return false;
        }
    }
    true
}

fn validate_dynamic_vertex(dyn: &DynamicGraph<usize>, v: EulerVertex) {
    for i in 0..dyn.max_level + 1 {
        assert!(dyn.euler[i].vertices[v.vertex].tree_edges.len() <= dyn.adjacency_hint);
        assert!(dyn.euler[i].vertices[v.vertex].tree_edges.capacity() == dyn.adjacency_hint);
    }
}

fn validate_singleton(
    dyn: &DynamicGraph<usize>,
    level: usize,
    item: (NodeIndex, EulerVertex),
) -> bool {
    let (i, v) = item;
    validate_dynamic_vertex(dyn, v);
    if v[EdgeDirection::Incoming].is_some() || v[EdgeDirection::Outgoing].is_some() {
        println!("Singleton {:?} = {:?} has adjacent edges", i, v);
        return false;
    }
    let edges = &dyn.euler[level].vertices[v.vertex].tree_edges;
    if edges.len() != 0 {
        println!("Singleton {:?} \nhas tree edge occurrences: {:?}", v, edges);
        return false;
    }
    true
}

fn validate_first(
    dyn: &DynamicGraph<usize>,
    level: usize,
    seq: &Vec<(NodeIndex, EulerVertex)>,
) -> bool {
    let (i, v) = seq[0];
    validate_dynamic_vertex(dyn, v);
    if let Some(inc) = v[EdgeDirection::Incoming] {
        let hv_inc = dyn.euler[level].vertices[v.vertex].tree_edges[inc];
        println!(
            "First {:?} = {:?} \nhas incoming {:?}",
            i, v, dyn.edges[hv_inc.edge]
        );
        return false;
    }
    if let Some(out) = v[EdgeDirection::Outgoing] {
        let hv_out = dyn.euler[level].vertices[v.vertex].tree_edges[out];
        if v != dyn.euler[level].forest[hv_out[EdgeDirection::Outgoing]] {
            println!(
                "First {:?} = {:?} \nhas incorrect outgoing {:?} \nfor outgoing {:?}",
                i, v, hv_out, dyn.edges[hv_out.edge]
            );
            return false;
        }
    } else {
        println!("First {:?} = {:?} \nhas no outgoing half edge", i, v);
        return false;
    }
    true
}

fn validate_inner(
    dyn: &DynamicGraph<usize>,
    level: usize,
    i: usize,
    seq: &Vec<(NodeIndex, EulerVertex)>,
) -> bool {
    let (i, v) = seq[i];
    validate_dynamic_vertex(dyn, v);
    if let Some(out) = v[EdgeDirection::Outgoing] {
        let hv_out = dyn.euler[level].vertices[v.vertex].tree_edges[out];
        if v != dyn.euler[level].forest[hv_out[EdgeDirection::Outgoing]] {
            println!(
                "Inner {:?} = {:?} \nhas incorrect outgoing {:?} \nfor outgoing {:?}",
                i, v, hv_out, dyn.edges[hv_out.edge]
            );
            return false;
        }
    } else {
        println!("Inner {:?} = {:?} has no outgoing half edge", i, v);
        return false;
    }
    if let Some(inc) = v[EdgeDirection::Incoming] {
        let hv_inc = dyn.euler[level].vertices[v.vertex].tree_edges[inc];
        if v != dyn.euler[level].forest[hv_inc[EdgeDirection::Incoming]] {
            println!(
                "Inner {:?} = {:?} \nhas incorrect incoming {:?} \nfor incoming {:?}",
                i, v, hv_inc, dyn.edges[hv_inc.edge]
            );
            return false;
        }
    } else {
        println!("Inner {:?} = {:?} has no incoming half edge", i, v);
        return false;
    }
    true
}

fn validate_last(
    dyn: &DynamicGraph<usize>,
    level: usize,
    seq: &Vec<(NodeIndex, EulerVertex)>,
) -> bool {
    let (i, v) = seq[seq.len() - 1];
    validate_dynamic_vertex(dyn, v);
    if let Some(out) = v[EdgeDirection::Outgoing] {
        let hv_out = dyn.euler[level].vertices[v.vertex].tree_edges[out];
        println!(
            "Last {:?} = {:?} \nhas outgoing {:?}",
            i, v, dyn.edges[hv_out.edge]
        );
        return false;
    }
    if let Some(inc) = v[EdgeDirection::Incoming] {
        let hv_inc = dyn.euler[level].vertices[v.vertex].tree_edges[inc];
        if v != dyn.euler[level].forest[hv_inc[EdgeDirection::Incoming]] {
            println!(
                "Last {:?} = {:?} \nhas incorrect incoming {:?} \nfor incoming {:?}",
                i, v, hv_inc, dyn.edges[hv_inc.edge]
            );
            return false;
        }
    } else {
        println!("Last {:?} = {:?} has no incoming half edge", i, v);
        return false;
    }
    true
}

fn euler_sequence(
    dyn: &DynamicGraph<usize>,
    level: usize,
    n: NodeIndex,
) -> Vec<(NodeIndex, EulerVertex)> {
    let t = BinaryInOrder::new(&dyn.euler[level].forest, n);
    t.fold(Vec::new(), |mut v, i| {
        v.push((i.0, *(i.1)));
        v
    })
}
