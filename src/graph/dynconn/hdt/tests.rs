use crate::prelude::*;
use rand;
use rand::Rng;
use std::mem::{size_of, size_of_val};
use super::{EdgeDirection, EdgeIndex, EulerVertex, VertexWeight};
use crate::tree::traversal::BinaryInOrder;

#[test]
fn test_basic_insert() {
    let mut dg: DynamicGraph<usize> = DynamicGraph::new(5, 3);
    let _e1 = dg.insert_edge(VertexIndex(0), VertexIndex(1));
    let _e2 = dg.insert_edge(VertexIndex(1), VertexIndex(2));
    let _e3 = dg.insert_edge(VertexIndex(3), VertexIndex(4));
    let _e4 = dg.insert_edge(VertexIndex(1), VertexIndex(3));
    let _e5 = dg.insert_edge(VertexIndex(2), VertexIndex(4));
    let e6 = dg.insert_edge(VertexIndex(0), VertexIndex(3));
    let _e7 = dg.insert_edge(VertexIndex(3), VertexIndex(1));
    dg.delete_edge(e6.unwrap());
    assert!(validate(&dg));
    assert!(dg.is_connected(VertexIndex(0), VertexIndex(4)));
}

#[test]
fn test_big_insert_and_delete() {
    let mut dg: DynamicGraph<usize> = DynamicGraph::new(50, 3);
    let mut edges = Vec::new();
    for i in 0..9 {
        edges.push(dg.insert_edge(VertexIndex(i), VertexIndex(i + 1)).unwrap());
        assert!(validate(&dg));
    }
    for i in 11..19 {
        edges.push(dg.insert_edge(VertexIndex(i), VertexIndex(i + 1)).unwrap());
        assert!(validate(&dg));
    }
    for i in 21..29 {
        edges.push(dg.insert_edge(VertexIndex(i), VertexIndex(i + 1)).unwrap());
        assert!(validate(&dg));
    }
    for i in 31..39 {
        edges.push(dg.insert_edge(VertexIndex(i), VertexIndex(i + 1)).unwrap());
        assert!(validate(&dg));
    }
    edges.push(dg.insert_edge(VertexIndex(4), VertexIndex(14)).unwrap());
    assert!(validate(&dg));
    edges.push(dg.insert_edge(VertexIndex(15), VertexIndex(25)).unwrap());
    assert!(validate(&dg));
    edges.push(dg.insert_edge(VertexIndex(26), VertexIndex(36)).unwrap());
    assert!(validate(&dg));

    for e in edges.iter() {
        dg.delete_edge(*e);
        assert!(validate(&dg));
    }
}

#[test]
fn test_big_insert_and_disconnect() {
    let mut dg: DynamicGraph<usize> = DynamicGraph::new(50, 3);
    let mut edges = Vec::new();
    for i in 0..9 {
        dg.insert_edge(VertexIndex(i), VertexIndex(i + 1)).unwrap();
        assert!(validate(&dg));
    }
    for i in 1..4 {
        dg.insert_edge(VertexIndex(i), VertexIndex(i * 2)).unwrap();
        assert!(validate(&dg));
    }
    for i in 11..19 {
        dg.insert_edge(VertexIndex(i), VertexIndex(i + 1)).unwrap();
        assert!(validate(&dg));
    }
    for i in 1..4 {
        dg.insert_edge(VertexIndex(i + 10), VertexIndex((i * 2) + 10))
            .unwrap();
        assert!(validate(&dg));
    }
    for i in 21..29 {
        dg.insert_edge(VertexIndex(i), VertexIndex(i + 1)).unwrap();
        assert!(validate(&dg));
    }
    for i in 1..4 {
        edges.push(
            dg.insert_edge(VertexIndex(i + 20), VertexIndex((i * 2) + 20))
                .unwrap(),
        );
        assert!(validate(&dg));
    }
    for i in 31..39 {
        dg.insert_edge(VertexIndex(i), VertexIndex(i + 1)).unwrap();
        assert!(validate(&dg));
    }
    for i in 1..4 {
        dg.insert_edge(VertexIndex(i + 30), VertexIndex((i * 2) + 30))
            .unwrap();
        assert!(validate(&dg));
    }
    dg.disconnect_component(VertexIndex(4));
    assert!(validate(&dg));
    dg.disconnect_component(VertexIndex(15));
    assert!(validate(&dg));
    dg.disconnect_component(VertexIndex(26));
    assert!(validate(&dg));
    dg.disconnect_component(VertexIndex(37));
    assert!(validate(&dg));

    assert!(dg.edges.edges.len() == 0);
    assert!(dg.ext_euler.forest.node_count() == 50);
    for i in 0..dg.max_level + 1 {
        assert!(dg.euler[i].forest.node_count() == 50);
    }
}

#[test]
fn test_big_random_insert_and_delete() {
    let mut dg: DynamicGraph<usize> = DynamicGraph::new(20, 10);
    let mut edges = Vec::new();
    let mut rng = rand::thread_rng();
    for _ in 0..100 {
        for _ in 0..10 {
            let src = VertexIndex(rng.gen::<usize>() % 20);
            let dst = VertexIndex(rng.gen::<usize>() % 20);
            let e = dg.insert_edge(src, dst);
            e.map(|edge| {
                edges.push(edge);
                assert!(validate(&dg));
            });
        }
        for _ in 0..5 {
            let e = rng.gen::<usize>() % edges.len();
            dg.delete_edge(edges[e]);
            edges.remove(e);
        }
    }
    for e in edges.iter() {
        dg.delete_edge(*e);
        assert!(validate(&dg));
    }
}

#[test]
fn test_complete_insert_delete() {
    let mut dg: DynamicGraph<usize> = DynamicGraph::new(100, 100);
    let mut edges = Vec::with_capacity(10000);

    for i in 0..100 {
        for j in 0..100 {
            dg.insert_edge(VertexIndex(i), VertexIndex(j))
                .map(|e| edges.push(e));
        }
    }
    for e in edges.iter() {
        dg.delete_edge(*e);
    }
    assert!(validate(&dg));
}

fn validate(dg: &DynamicGraph<usize>) -> bool {
    let components: Vec<VertexIndex> = dg.components().collect();
    let mut n_components = 0;
    for level in 0..dg.max_level {
        for i in 0..dg.euler[level].vertices.vertices.len() {
            let n = dg.euler[level].vertices.vertices[i].active_node;
            if dg.euler[level].forest.weight(n).map_or(0, |w| w.act_count) != 1 {
                println!(
                    "{:?} ({:?}) should be active at level {:?}",
                    VertexIndex(i),
                    n,
                    level
                );
                return false;
            }
            if level == 0 {
                let edge_count_check = dg
                    .component_vertices(VertexIndex(i))
                    .flat_map(move |v| dg.edges.edges.iter().filter(move |e| e.1.src == v))
                    .count();
                let edge_count = dg.component_edges(VertexIndex(i)).count();
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
        for i in 3..((dg.euler[level].vertices.vertices.len() * 2) + 3) {
            assert!(
                dg.ext_euler.forest.value(NodeIndex(i)).is_none()
                    || size_of_val(
                    &dg.ext_euler
                        .forest
                        .weight(NodeIndex(i))
                        .map_or(VertexWeight::default(), |w| *w)
                ) == 3 * size_of::<usize>()
            );
            assert!(
                dg.euler[level].forest.value(NodeIndex(i)).is_none()
                    || size_of_val(
                    &dg.euler[level]
                        .forest
                        .weight(NodeIndex(i))
                        .map_or(VertexWeight::default(), |w| *w)
                ) == 2 * size_of::<usize>()
            );
            if dg.euler[level].forest.value(NodeIndex(i)).is_none() {
                continue;
            }
            if dg.euler[level]
                .forest
                .weight(NodeIndex(i))
                .map_or(0, |w| w.act_count)
                != 0
            {
                if dg.euler[level].vertices[dg.euler[level].forest[NodeIndex(i)].vertex]
                    .active_node
                    != NodeIndex(i)
                {
                    println!("{:?} should be active at level {:?}", NodeIndex(i), level);
                    return false;
                }
            }
            if dg.euler[level].forest.parent(NodeIndex(i)).is_none() {
                if level == 0 {
                    let vertex = dg.euler[0].forest[NodeIndex(i)].vertex;
                    n_components += 1;
                    if !components.contains(&vertex) {
                        println!(
                            "Component root {:?} not contained in component list",
                            vertex
                        );
                        return false;
                    }
                }
                if validate_component(dg, level, NodeIndex(i)) == false {
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
    for item in dg.edges.edges.iter() {
        let idx = EdgeIndex(item.0);
        let e = *(item.1);
        if e.is_tree_edge == true {
            if dg.ext_euler.is_connected(e.src, e.dst) == false {
                println!("Tree {:?} not connected in external forest", e);
                return false;
            }
            for i in 0..(dg.max_level + 1) {
                if i <= e.level {
                    if dg.euler[i].is_connected(e.src, e.dst) == false {
                        println!("Tree {:?} not connected at level {:?}", e, i);
                        return false;
                    }
                } else {
                    if dg.euler[i].is_connected(e.src, e.dst) == true {
                        println!("Tree {:?} connected at level {:?}", e, i);
                        return false;
                    }
                }
            }
        } else {
            if dg.ext_euler.is_connected(e.src, e.dst) == false {
                println!("Non tree {:?} not connected in external forest", e);
                return false;
            }
            if dg.is_connected(e.src, e.dst) == false {
                println!("is_connected() == false for non tree {:?}", e);
                return false;
            } else {
                for i in 0..(dg.max_level + 1) {
                    if i == e.level {
                        if dg.euler[i].adjacent_edge_index(e.src, idx).is_none() {
                            println!(
                                "Non tree {:?} not found in adj_edges[{:?}][{:?}]",
                                e, i, e.src
                            );
                            return false;
                        }
                        if dg.euler[i].adjacent_edge_index(e.dst, idx).is_none() {
                            println!(
                                "Non tree {:?} not found in adj_edges[{:?}][{:?}]",
                                e, i, e.dst
                            );
                            return false;
                        }
                    } else {
                        if dg.euler[i].adjacent_edge_index(e.src, idx).is_some() {
                            println!("Non tree {:?} found in adj_edges[{:?}][{:?}]", e, i, e.src);
                            return false;
                        }
                        if dg.euler[i].adjacent_edge_index(e.dst, idx).is_some() {
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

fn validate_component(dg: &DynamicGraph<usize>, level: usize, n: NodeIndex) -> bool {
    let max_size = ((dg.size as f64) / (2.0_f64).powi(level as i32)).floor() as usize;
    let act_size = dg.euler[level]
        .forest
        .subweight(n)
        .map_or(0, |w| w.act_count);
    if act_size > max_size {
        println!(
            "Component size of {:?} at level {:?} = {:?} > max = {:?}",
            dg.euler[level].forest[n], level, act_size, max_size
        );
        return false;
    }

    let seq = euler_sequence(dg, level, n);
    if seq.len() == 1 {
        return validate_singleton(dg, level, seq[0]);
    } else {
        if validate_first(dg, level, &seq) == false {
            return false;
        }
        for i in 1..seq.len() - 1 {
            if validate_inner(dg, level, i, &seq) == false {
                return false;
            }
        }
        if validate_last(dg, level, &seq) == false {
            return false;
        }
    }
    true
}

fn validate_dynamic_vertex(dg: &DynamicGraph<usize>, v: EulerVertex) {
    for i in 0..dg.max_level + 1 {
        assert!(dg.euler[i].vertices[v.vertex].tree_edges.len() <= dg.adjacency_hint);
        assert!(dg.euler[i].vertices[v.vertex].tree_edges.capacity() == dg.adjacency_hint);
    }
}

fn validate_singleton(
    dg: &DynamicGraph<usize>,
    level: usize,
    item: (NodeIndex, EulerVertex),
) -> bool {
    let (i, v) = item;
    validate_dynamic_vertex(dg, v);
    if v[EdgeDirection::Incoming].is_some() || v[EdgeDirection::Outgoing].is_some() {
        println!("Singleton {:?} = {:?} has adjacent edges", i, v);
        return false;
    }
    let edges = &dg.euler[level].vertices[v.vertex].tree_edges;
    if edges.len() != 0 {
        println!("Singleton {:?} \nhas tree edge occurrences: {:?}", v, edges);
        return false;
    }
    true
}

fn validate_first(
    dg: &DynamicGraph<usize>,
    level: usize,
    seq: &Vec<(NodeIndex, EulerVertex)>,
) -> bool {
    let (i, v) = seq[0];
    validate_dynamic_vertex(dg, v);
    if let Some(inc) = v[EdgeDirection::Incoming] {
        let hv_inc = dg.euler[level].vertices[v.vertex].tree_edges[inc];
        println!(
            "First {:?} = {:?} \nhas incoming {:?}",
            i, v, dg.edges[hv_inc.edge]
        );
        return false;
    }
    if let Some(out) = v[EdgeDirection::Outgoing] {
        let hv_out = dg.euler[level].vertices[v.vertex].tree_edges[out];
        if v != dg.euler[level].forest[hv_out[EdgeDirection::Outgoing]] {
            println!(
                "First {:?} = {:?} \nhas incorrect outgoing {:?} \nfor outgoing {:?}",
                i, v, hv_out, dg.edges[hv_out.edge]
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
    dg: &DynamicGraph<usize>,
    level: usize,
    i: usize,
    seq: &Vec<(NodeIndex, EulerVertex)>,
) -> bool {
    let (i, v) = seq[i];
    validate_dynamic_vertex(dg, v);
    if let Some(out) = v[EdgeDirection::Outgoing] {
        let hv_out = dg.euler[level].vertices[v.vertex].tree_edges[out];
        if v != dg.euler[level].forest[hv_out[EdgeDirection::Outgoing]] {
            println!(
                "Inner {:?} = {:?} \nhas incorrect outgoing {:?} \nfor outgoing {:?}",
                i, v, hv_out, dg.edges[hv_out.edge]
            );
            return false;
        }
    } else {
        println!("Inner {:?} = {:?} has no outgoing half edge", i, v);
        return false;
    }
    if let Some(inc) = v[EdgeDirection::Incoming] {
        let hv_inc = dg.euler[level].vertices[v.vertex].tree_edges[inc];
        if v != dg.euler[level].forest[hv_inc[EdgeDirection::Incoming]] {
            println!(
                "Inner {:?} = {:?} \nhas incorrect incoming {:?} \nfor incoming {:?}",
                i, v, hv_inc, dg.edges[hv_inc.edge]
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
    dg: &DynamicGraph<usize>,
    level: usize,
    seq: &Vec<(NodeIndex, EulerVertex)>,
) -> bool {
    let (i, v) = seq[seq.len() - 1];
    validate_dynamic_vertex(dg, v);
    if let Some(out) = v[EdgeDirection::Outgoing] {
        let hv_out = dg.euler[level].vertices[v.vertex].tree_edges[out];
        println!(
            "Last {:?} = {:?} \nhas outgoing {:?}",
            i, v, dg.edges[hv_out.edge]
        );
        return false;
    }
    if let Some(inc) = v[EdgeDirection::Incoming] {
        let hv_inc = dg.euler[level].vertices[v.vertex].tree_edges[inc];
        if v != dg.euler[level].forest[hv_inc[EdgeDirection::Incoming]] {
            println!(
                "Last {:?} = {:?} \nhas incorrect incoming {:?} \nfor incoming {:?}",
                i, v, hv_inc, dg.edges[hv_inc.edge]
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
    dg: &DynamicGraph<usize>,
    level: usize,
    n: NodeIndex,
) -> Vec<(NodeIndex, EulerVertex)> {
    let t = BinaryInOrder::new(&dg.euler[level].forest, n);
    t.fold(Vec::new(), |mut v, i| {
        v.push((i.0, *(i.1)));
        v
    })
}
