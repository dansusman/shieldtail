open Printf
module NeighborSet = Set.Make (String)

type neighborst = NeighborSet.t

module Graph = Map.Make (String)

type grapht = neighborst Graph.t

module StringSet = Set.Make (String)

type livet = StringSet.t

let empty : grapht = Graph.empty

let merge_two (g1 : grapht) (g2 : grapht) : grapht =
  Graph.union (fun _ name1 name2 -> Some (StringSet.union name1 name2)) g1 g2
;;

let add_node (g : grapht) (name : string) : grapht =
  if Graph.mem name g then g else Graph.add name NeighborSet.empty g
;;

let add_directed_edge (g : grapht) (n1 : string) (n2 : string) : grapht =
  let g' = add_node (add_node g n1) n2 in
  let curr_neighbors = Graph.find n1 g' in
  Graph.add n1 (NeighborSet.add n2 curr_neighbors) g'
;;

let add_edge (g : grapht) (n1 : string) (n2 : string) : grapht =
  if n1 = n2
  then g
  else
    let g' = add_directed_edge g n1 n2 in
    add_directed_edge g' n2 n1
;;

let add_edges (g : grapht) (n : string) (others : neighborst) : grapht =
  StringSet.fold (fun other prev_graph -> add_edge prev_graph n other) others g
;;

(* adds an edge between each node in the set to each other node *)
let add_pairwise_edges (g : grapht) (nodes : neighborst) : grapht =
  let new_graph = StringSet.fold (fun prev_graph n -> add_node n prev_graph) nodes g in
  StringSet.fold (fun n prev_graph -> add_edges prev_graph n nodes) nodes new_graph
;;

(* adds all of the others as neighbors of n and vice versa*)
let init_with_edges (n : string) (others : neighborst) : grapht =
  add_edges (Graph.singleton n StringSet.empty) n others
;;

let get_neighbors (g : grapht) (name : string) : string list =
  if Graph.mem name g then NeighborSet.fold (fun n ns -> n :: ns) (Graph.find name g) [] else []
;;

let remove_neighbor (g : grapht) (from : string) (neighbor : string) : grapht =
  let new_neighbors = List.filter (fun n -> n != neighbor) (get_neighbors g from) in
  let new_neighbors_set = StringSet.of_list new_neighbors in
  Graph.add from new_neighbors_set (Graph.remove from g)
;;

let get_vertices (g : grapht) : string list =
  let keys, _ = List.split (Graph.bindings g) in
  keys
;;

let remove_node (g : grapht) (name : string) : grapht =
  List.fold_right
    (fun neighbor prev_graph -> remove_neighbor prev_graph neighbor name)
    (get_neighbors g name) (Graph.remove name g)
;;

let string_of_graph (g : grapht) : string =
  let string_of_neighbors (n : string) : string = ExtString.String.join ", " (get_neighbors g n) in
  ExtString.String.join "\n"
    (List.map (fun k -> sprintf "%s: %s" k (string_of_neighbors k)) (get_vertices g))
;;

let graph_to_viz (g : grapht) : string =
  let prefix = "digraph G { \n" in
  let suffix = "}\n" in
  let nodes = ExtString.String.join "\n" (List.map (fun k -> sprintf "%s" k) (get_vertices g)) in
  let edges =
    ExtString.String.join "\n"
      (List.map
         (fun k ->
           ExtString.String.join "\n"
             (List.map (fun n -> sprintf "%s -> %s" k n) (get_neighbors g k)) )
         (get_vertices g) )
  in
  prefix ^ nodes ^ edges ^ suffix
;;
