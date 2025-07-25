Require Import Ltac2.Init.
Require Import tensorexpression_int.
Require Import FSetExtra.
Require hypercaml_testing. 
Require UTest.

(* Change which interface we import here to change which 
  graph implementation we use 
  (Currently available:
  - HypercamlInterface for the ltac2 bindings for hypercaml
  - hygergraph_compat.HypermutInterface for ltac2 mutable hypergraphs
  - hygergraph_immutable_compat.HyperimmutInterface for ltac2 
      immutable hypergraphs
  )*)
Require Import HypercamlInterface.

Module StringExtra.

Ltac2 list_of_string (s : string) : char list :=
  List.map (fun i => String.get s i) (List.range 0 (String.length s)).

Ltac2 string_of_list (cs : char list) : string :=
  let s := String.make (List.length cs) (Char.of_int 0) in
  List.iter (fun (i,c) => String.set s i c) (List.enumerate cs);
  s.

End StringExtra. 

Module StringOfInt_dec.

Ltac2 zero_CHAR := 48.
Ltac2 nine_CHAR := 57.

Import StringExtra.

Ltac2 string_of_int (n : int) : string := 
  Message.to_string (Message.of_int n).

Ltac2 digit_of_char (c : char) : int option :=
  let c := Char.to_int c in 
  if Int.lt c zero_CHAR then None (* Too low *) else 
  if Int.lt nine_CHAR c then None (* Too high *) else
  Some (Int.sub c 48).

Ltac2 int_of_digit_list (ds : int list) : int :=
  List.fold_left (fun acc d => Int.add (Int.mul acc 10) d) 0 ds.

Ltac2 int_of_char_list (cs : char list) : int option :=
  let may_ds := List.fold_right (fun c may_ds => 
    Option.bind may_ds (fun ds => 
    Option.map (fun d => d :: ds) (digit_of_char c) )) cs (Some []) in 
  Option.map int_of_digit_list may_ds.

Ltac2 int_of_string (s : string) : int option :=
  int_of_char_list (list_of_string s).

Module Testing.
(* TODO: Testing! *)

(* UTest.... *)

(* Ltac2 Eval string_of_int 01234567890.
Ltac2 Eval int_of_string (string_of_int 01234567890). *)

(* Ltac2 Eval int_of_string (string_of_int -1). *)

End Testing.

End StringOfInt_dec.

Module StringOfInt_hex.

Import StringExtra.

Ltac2 zero_CHAR := 48.
Ltac2 nine_CHAR := 57.
Ltac2 a_CHAR := 65.
Ltac2 f_CHAR := 70.

Ltac2 _char_of_digit (n : int) : char :=
  (* NOTE: We assume 0 <= n < 16 *)
  if Int.lt n 10 then 
  Char.of_int (Int.add zero_CHAR n) else
  Char.of_int (Int.add a_CHAR (Int.sub n 10)).

Ltac2 digit_of_char (c : char) : int option :=
  let c := Char.to_int c in 
  if Int.lt c zero_CHAR then None else
  if Int.le c nine_CHAR then Some (Int.sub c zero_CHAR) else
  if Int.lt c a_CHAR then None else 
  if Int.le c f_CHAR then Some (Int.sub c a_CHAR) else None.

Ltac2 char_list_of_int (n : int) : char list :=
  if Int.lt n 0 then 
    Control.throw_invalid_argument "Negative argument to char_list_of_int" else
  let rec chars n : char list :=
    if Int.lt n 16 then 
      [_char_of_digit n]
    else
      let upper := chars (Int.div n 16) in 
      List.append upper [_char_of_digit (Int.mod n 16)]
  in 
  chars n.

Ltac2 int_of_digit_list (ds : int list) : int :=
  List.fold_left (fun acc d => Int.add (Int.mul acc 16) d) 0 ds.

Ltac2 int_of_char_list (cs : char list) : int option :=
  let may_ds := List.fold_right (fun c may_ds => 
    Option.bind may_ds (fun ds => 
    Option.map (fun d => d :: ds) (digit_of_char c) )) cs (Some []) in 
  Option.map int_of_digit_list may_ds.


Ltac2 string_of_int (n : int) : string := 
  string_of_list (char_list_of_int n).

Ltac2 int_of_string (s : string) : int option :=
  int_of_char_list (list_of_string s).

Module Testing.
(* TODO: Testing! *)

(* UTest.... *)

(* Ltac2 Eval string_of_int 0x0123456789ABCDEF0.
Ltac2 Eval int_of_string (string_of_int 0x123456789ABCDEF). *)

(* Ltac2 Eval int_of_string (string_of_int -1). *)

End Testing.

End StringOfInt_hex.

Module NumericalGraphs.

(* Change this to change how indices are represented in 
  graphs corresponding to tensor expressions *)
Import StringOfInt_dec.

Import Printf.

(* Convert a [TensorList] to the corresponding hypergraph. 
  The conversion is, essentially, that contractions become 
  (internal) vertices, abstract tensors become hyperedges,
  deltas become free wires, and any free lower / upper indices
  in the abstract tensors become input / output vertices,
  respectively.

  Vertices are labeled by the [TypeIdx] from the contraction
  or input, while edges are labeled by the [AbsIdx] indexing
  their function. *)
Ltac2 tensor_list_to_hypergraph (t : TensorList) : Graph.t :=
  let of_ty (t : TypeIdx) : string option := 
    if Int.equal t (-1) then None else Some (string_of_int t) in 
  (* Start with an empty graph *)
  let g := Graph.make () in 
  (* First, add a vertex for each contraction, recording their indices *)
  let (g, cs_map) := List.fold_left (fun (g, mp) (ty, a, b) => 
    (* printf "Looking at contraction K{%i}_[%i]^[%i]" ty a b; *)
    let (g, i) := Graph.add_vertex (of_ty ty) None g in 
    g, (i, (ty, a, b))::mp) (g, []) (t.(contractions)) in

  (* Then, for each abstract tensor, add a hyperedge, adding vertices for
    each free index, recording them in [in_verts] and [out_verts] as we do
    (they will be marked as appropriately in / out later) *)
  let (g, in_verts, out_verts, _contr_edges) := (* ([], [], []) *)
    List.fold_right (fun (abs_idx, lower, upper) (g, ins, outs, contrs) => 
      (* First, get the list of source/lower vertices, adding those we lack *)
      let (g, new_ins, s) := List.fold_left (fun (g, ins, s) (ty, a) => (* TODO: Fold left so we can [cons] to [s] rather than appending? *)
        (* Try to find an internal/contraction vertex with the right label, i.e. 
          a contraction with [a] as an _lower_ index (TODO: Check, but I think lower is correct here) *)
        let may_i := List.find_opt (fun (_, (ty', a', _)) =>
          Bool.and (Int.equal ty ty') (Int.equal a a')) cs_map in 
        match may_i with 
        | Some (i, _) => (* Found a matching vertex; add it to the source vertex list *)
          (g, ins, List.append s [i])
        | None => (* No matching vertex means this is a free index; add it as a vertex marked to be made an input *)
          let (g, i) := Graph.add_vertex (of_ty ty) None g in 
          (g, List.append ins [i], List.append [i] s)
        end) (g, [], []) lower in 
      (* Next, do the same for the target/upper vertices *)
      let (g, new_outs, t) := List.fold_left (fun (g, outs, t) (ty, b) => (* TODO: Fold left so we can [cons] to [t] rather than appending? *)
        (* Try to find an internal/contraction vertex with the right label, i.e. 
          a contraction with [b] as an _upper_ index (TODO: Check, but I think upper is correct here) *)
        let may_i := List.find_opt (fun (_, (ty', _, b')) =>
          Bool.and (Int.equal ty ty') (Int.equal b b')) cs_map in 
        match may_i with 
        | Some (i, _) => (* Found a matching vertex; add it to the source vertex list *)
          (g, outs, List.append t [i])
        | None => (* No matching vertex means this is a free index; add it as a vertex marked to be made an input *)
          let (g, i) := Graph.add_vertex (of_ty ty) None g in 
          (g, List.append outs [i], List.append [i] t)
        end) (g, [], []) upper in
      (* Now, we can add the edge to the graph *) 
      let (g, e) := Graph.add_edge (of_ty abs_idx) None s t g in
      (* Finally, record the new input / output vertices we'll need to mark, 
      along with the edge index of this edge *)
      (g, List.append new_ins ins, List.append new_outs outs, 
        List.cons (e, (abs_idx, lower, upper)) contrs) (* TODO: Remove unused lower / upper values here *)
      ) (t.(abstracts)) (g, [], [], []) in 
  (* Finally, add a vertex and edge for each delta *)
  let (g, delta_ins, delta_outs, _delta_es) := List.fold_right 
    (fun (ty, _a, _b) (g, dins, douts, des) => 
    (* Make input and output vertices *)
    let (g, a_idx) := Graph.add_vertex (of_ty ty) None g in 
    let (g, b_idx) := Graph.add_vertex (of_ty ty) None g in 
    (* Make an edge for the delta with these as source and target *)
    let (g, e_idx) := Graph.add_edge None None [a_idx] [b_idx] g in 
    (* Record the new values *)
    (g, List.append dins [a_idx], List.append douts [b_idx], List.append des [e_idx])
    ) (t.(deltas)) (g, [], [], []) in 
  (* Now, the graph has all the data we need, and we just need to set 
    the inputs and outputs *)
  let g := Graph.set_inputs (List.append in_verts delta_ins) g in 
  let g := Graph.set_outputs (List.append out_verts delta_outs) g in
  (* Then our graph is ready! *)
  g.

Import Printf.

(* Construct a [TensorList] from a (restricted form of a) hypergraph: 
  specifically, the only edges that will end up in the [TensorList] 
  are those with non-empty value, which will become AbstractTensors,
  and those with empty value and singleton sources and targets, which
  will become Deltas. We use vertex indices as label indexes. All vertices
  must have (non-empty) values, which are used as their types. *)
Ltac2 hypergraph_to_tensor_list (g : Graph.t) : TensorList :=
  let to_ty (s : string) : TypeIdx option := int_of_string s in
  (* Establish the mapping between indices and types *)
  let vertex_type_map := 
    FMap.mapi (fun v vd => 
    (* printf "Looking at vertex %i of type %s" v (VData.value vd); *)
    let ty := match VData.value vd with 
    | "" => printf "WARNING: trying to convert graph to TensorList, but vertex %i has no value (type). Placeholder value -1 will be used" v;
      -1
    | lbl => 
      match to_ty lbl with 
      | Some ty => ty
      | None => printf "WARNING: trying to convert graph to TensorList, but vertex %i has non-numeric value (type) %s. Placeholder value -1 will be used" v lbl;
        -1
      end
    end in 
    ty) (Graph.vdata g) in 
  let vertex_type v := match FMap.find_opt v vertex_type_map with
    | Some ty => ty
    | None => printf "ERROR: while trying to convert graph to TensorList, tried to find type of vertex %i, but this vertex does not seem to appear in the graph." v;
      Control.throw (Not_found)
    end in 
  let lower_map v := v in (* Int.lsl v 1 in (* double *) *)
  let upper_map v := v in (* Int.lxor (Int.lsl v 1) 1 in (* double and add 1*) *)
  (* Construct abstract tensors and deltas from the edges *)
  let (abstracts, deltas) := FMap.fold (fun e ed (abs, ds) => 
    (* Look at the value of the edge *)
    match EData.value ed with 
    | "" => (* Empty edges must have singleton sources and targets 
      of the same type, in which case they become deltas *)
      if Bool.and (Int.equal (List.length (EData.source ed)) 1)
          (Int.equal (List.length (EData.target ed)) 1) then 
        (* This is almost a valid delta; test types *)
        let a := List.hd (EData.source ed) in 
        let b := List.hd (EData.target ed) in 
        let ty_a := vertex_type a in 
        let ty_b := vertex_type b in 
        if Int.equal ty_a ty_b  then
        (* This is a valid delta! *)
          (abs, List.cons (ty_a, lower_map a, upper_map b) ds)
        else 
          (printf "WARNING: singleton edge (%i) between vertices %i and %i have different types (%i and %i). Edge will be ignored!" e a b ty_a ty_b;
          (abs, ds))
      else 
        (printf "WARNING: valueless edge %i is not singleton. It will be ignored!" e;
        (abs, ds))
    | lbl => (* Edge has a value, so will become an AbstractTensor *)
      let abs_idx := match to_ty lbl with
        | None => printf "WARNING: trying to convert graph to TensorList, but edge %i has non-numeric value (type) %s. Placeholder value -1 will be used" e lbl;
          -1
        | Some ty => ty 
        end in 
      let lower := List.map (fun v => (vertex_type v, lower_map v)) (EData.source ed) in 
      let upper := List.map (fun v => (vertex_type v, upper_map v)) (EData.target ed) in 
      (List.cons (abs_idx, lower, upper) abs, ds)
    end)
  (Graph.edata g) ([], []) in 
  
  (* Now, we use the internal vertices to make our contractions *)
  let contractions := FMap.fold (fun v _vd cs => 
    if Graph.is_boundary g v then 
      (* Boundary vertex; do nothing *)
      cs else
    (* Internal vertex; this becomes a contraction *)
    let ty := vertex_type v in 
    List.append cs [(ty, lower_map v, upper_map v)]
    ) (Graph.vdata g) [] in 
  
  (* Finally, we have all our data *)
  mk_tensorlist contractions deltas abstracts.


Module Testing.

Module NumGraphExs.

Import Printing.

Ltac2 of_ty (ty : int) : string option := Some (string_of_int ty).
Ltac2 to_ty (ty : string) : int option := int_of_string ty.

(* Create a simple graph with two vertices connected by an edge *)
Ltac2 make_simple_graph (ty : int) : Graph.t :=
  let g := Graph.make () in
  let (g, v1) := Graph.add_vertex None None g in
  let (g, v2) := Graph.add_vertex None None g in
  let (g, _) := Graph.add_edge (of_ty ty) None [v1] [v2] g in
  let g := Graph.set_outputs [v2] (Graph.set_inputs [v1] g) in 
  g.



(* Create a cycle graph of 3 vertices and 3 edges *)
Ltac2 make_cycle_graph : unit -> Graph.t := fun () =>
  let g := Graph.make () in
  let (g, v1) := Graph.add_vertex (Some "1") None g in
  let (g, v2) := Graph.add_vertex (Some "1") None g in
  let (g, v3) := Graph.add_vertex (Some "1") None g in
  let (g, _) := Graph.add_edge (Some "1") None [v1] [v2] g in
  let (g, _) := Graph.add_edge (Some "1") None [v2] [v3] g in
  let (g, _) := Graph.add_edge (Some "1") None [v3] [v1] g in
  g.

(* Create a cycle graph of 3 vertices and 3 edges with nonequal values (types) *)
Ltac2 make_cycle_graph_inhomog : unit -> Graph.t := fun () =>
  let g := Graph.make () in
  let (g, v1) := Graph.add_vertex (Some "1") None g in
  let (g, v2) := Graph.add_vertex (Some "1") None g in
  let (g, v3) := Graph.add_vertex (Some "1") None g in
  let (g, _) := Graph.add_edge (of_ty 0) None [v1] [v2] g in
  let (g, _) := Graph.add_edge (of_ty 1) None [v2] [v3] g in
  let (g, _) := Graph.add_edge (of_ty 2) None [v3] [v1] g in
  g.


(* Create a path graph (vertices connected in a line) *)
Ltac2 make_path_graph (values : int list) :=
  let g := Graph.make () in
  let rec add_vertices g := fun l => match l with 
    | [] => (g, [])
    | v :: rest =>
        let (g, vid) := Graph.add_vertex (of_ty v) None g in
        let (g, rest_vids) := add_vertices g rest in
        (g, vid :: rest_vids)
    end
  in
  let (g, vertex_ids) : Graph.t * (int list) := add_vertices g values in
  let rec add_edges g (vertices : int list) edge_num := match vertices with
    | [] => g
    | v1 :: rest' => match rest' with 
    | [] => g
    | v2 :: rest => 
        let (g, _) := Graph.add_edge (Some ((string_of_int edge_num))) None [v1] [v2] g in
        add_edges g (v2 :: rest) (Int.add edge_num 1)
    end
    end
  in
  add_edges g vertex_ids 1.

(* Create a hypergraph with scalar edges (0-ary edges) *)
Ltac2 make_scalar_graph : unit -> Graph.t := fun () =>
  let g := Graph.make () in
  let (g, _) := Graph.add_edge (Some "1") None [] [] g in
  let (g, _) := Graph.add_edge (Some "2") None [] [] g in
  g.

(* Create a star graph (one central vertex connected to multiple leaves) *)
Ltac2 make_star_graph (center_value : int) (leaf_values : int list) : Graph.t :=
  let g := Graph.make () in
  let (g, center) := Graph.add_vertex (of_ty center_value) None g in
  let rec add_leaves g leaves_remaining edge_num := match leaves_remaining with
    | [] => g
    | leaf_val :: rest =>
        let (g, leaf) := Graph.add_vertex (of_ty leaf_val) None g in
        let (g, _) := Graph.add_edge (of_ty edge_num) None [center] [leaf] g in
        add_leaves g rest (Int.add edge_num 1)
    end
  in
  add_leaves g leaf_values 1.

(* Create a hypergraph with a proper multi-edge *)
Ltac2 make_hgraph : unit -> Graph.t := fun () =>
  let g := Graph.make () in
  let (g, v1) := Graph.add_vertex None None g in
  let (g, v2) := Graph.add_vertex None None g in
  let (g, v3) := Graph.add_vertex None None g in
  let (g, v4) := Graph.add_vertex None None g in
  let (g, _) := Graph.add_edge (Some "1") None [v1; v2] [v3] g in
  let (g, _) := Graph.add_edge (Some "2") None [v3] [v4] g in
  let g := Graph.set_outputs [v4] (Graph.set_inputs [v1; v2] g) in
  g.

(* Create a larger hypergraph with a proper multi-edge *)
Ltac2 make_hgraph2 : unit -> Graph.t := fun () =>
  let g := Graph.make () in
  let (g, v1) := Graph.add_vertex None None g in
  let (g, v2) := Graph.add_vertex None None g in
  let (g, v3) := Graph.add_vertex None None g in
  let (g, v4) := Graph.add_vertex None None g in
  let (g, v5) := Graph.add_vertex None None g in
  let (g, _) := Graph.add_edge (Some "1") None [v1; v2] [v3] g in
  let (g, _) := Graph.add_edge (Some "2") None [v3] [v4] g in
  let (g, _) := Graph.add_edge (Some "2") None [v4] [v5] g in
  let g := Graph.set_outputs [v5] (Graph.set_inputs [v1; v2] g) in
  g.

(* Create a graph with boundary inputs/outputs *)
Ltac2 make_boundary_graph : unit -> Graph.t := fun () =>
  let g := Graph.make () in
  let (g, v1) := Graph.add_vertex (Some "input") None g in
  let (g, v2) := Graph.add_vertex (Some "middle") None g in
  let (g, v3) := Graph.add_vertex (Some "output") None g in
  let (g, _) := Graph.add_edge (Some "process") None [v1] [v2] g in
  let (g, _) := Graph.add_edge (Some "result") None [v2] [v3] g in
  let g := Graph.set_outputs [v3] (Graph.set_inputs [v1] g) in
  g.


Ltac2 triangle_graph (ub : int) : Graph.t :=
  let g := Graph.make () in 
  let rnge := List.range 0 ub in 
  let g := List.fold_left (fun g i => 
    fst (Graph.add_vertex (Some (string_of_int (Int.div i 2))) 
      (Some i) g)) g rnge in
  let g := List.fold_right (fun i g => 
    fst (Graph.add_edge (Some (string_of_int i)) (Some i)
      (List.firstn i rnge) (List.skipn i rnge) g)) rnge g in
  g.

End NumGraphExs.

Import NumGraphExs.

Import Printing.

Ltac2 roundtrip_graph (g : Graph.t) : Graph.t :=
  tensor_list_to_hypergraph (hypergraph_to_tensor_list g).

Ltac2 print_graph (g : Graph.t) : unit :=
  Message.print (Graph.print_nice g).

Ltac2 print_match (m : Match.t) : unit :=
  print (Match.print_nice m).

Ltac2 print_match_full (m : Match.t) : unit :=
  print (Match.print_nice_full m).

Ltac2 test_roundtrip_eq (name : string) (f : unit -> Graph.t) : UTest.t :=
  UTest.value_eq_pr Graph.equal Graph.print_nice
    (f)
    (fun () => roundtrip_graph (f ()))
    (String.concat "" ["Graph "; name; " should be equal after roundtrip"]).

Ltac2 test_roundtrip_eqv (name : string) (f : Graph.t) : UTest.t :=
  UTest.value_eqv_pr Graph.equal Graph.print_nice
    (String.concat "" ["Graph "; name; " should be equal after roundtrip"])
    (f) (roundtrip_graph f).

Ltac2 test_roundtrip_iso (name : string) (f : Graph.t) : UTest.t :=
  UTest.opt_is_some_pr Match.print_nice_full
    (String.concat "" ["Graph "; name; " should be isomorphic after roundtrip"])
    (Match.find_iso (f) (roundtrip_graph f)).

Ltac2 test_triangle_graph () : UTest.t :=
  UTest.foreach [0;1;2;5;10] (fun ub => 
  test_roundtrip_eqv (String.app "triangle graph of size " (string_of_int ub))
  (triangle_graph ub)).

Ltac2 test_simple_graph () : UTest.t :=
  UTest.foreach [0;1;5] (fun i => test_roundtrip_eqv 
  (String.app "simple graph with edge value " (string_of_int i))
  (make_simple_graph i)).

Ltac2 test_cycle_graph () : UTest.t :=
  test_roundtrip_iso 
  ("cycle graph of size 3")
  (make_cycle_graph ()).

Ltac2 Eval UTest.check test_triangle_graph.
Ltac2 Eval UTest.check test_cycle_graph.

Import hypercaml_testing. 
Import caml_test_graphs.

Ltac2 print_tensor_of_graph (g : Graph.t) : unit :=
  Message.print (print_tensorlist (hypergraph_to_tensor_list g)).

(* Ltac2 Eval print_graph (roundtrip_graph ) *)

(* Ltac2 Eval print_tensor_of_graph (make_cycle_graph ()).
  (!Graph  ->  :  f (0) : 0 -> 1; 
    g (1) : 1 -> 2;  h (2) : 2 -> 0). *)


(* Ltac2 Eval print_graph (make_simple_graph 5).
Ltac2 Eval print_tensor_of_graph (make_simple_graph 5).
Ltac2 Eval print_graph (roundtrip_graph (make_simple_graph 5)). *)

Ltac2 Eval Graph.equal (triangle_graph 5) (roundtrip_graph (triangle_graph 5)).

(* Ltac2 Eval Graph.equal (make_simple_graph 5) (roundtrip_graph (make_simple_graph 5)).
Ltac2 Eval Match.find_iso (make_simple_graph 5) (roundtrip_graph (make_simple_graph 5)). *)






End Testing.


End NumericalGraphs.




Import Printing.


(* 
Ltac2 test_tensorlist (ub : int) : TensorList :=
  hypergraph_to_tensor_list (test_graph ub).

Ltac2 test_tensorexpr (ub : int) : TensorExpr :=
  tensor_expr_of_tensor_list (hypergraph_to_tensor_list (test_graph ub)). *)

(* Testing tensor_expression_to_simplified: *)
  (* First, the initial tensorlist: *)
  (* Ltac2 Eval Message.print (print_tensorlist (
            (test_tensorlist 5))). *)
  (* Then, the tensorlist having been made an expression: *)
  (* Ltac2 Eval Message.print (print_tensorlist (
    tensor_expression_to_simplified (
          tensor_expr_of_tensor_list
          (test_tensorlist 5)))). *)


(* Performance of this test was quadratic: 
5 -> 0.009, 10 -> 0.03, 15 -> 0.06, 20 -> 0.068, 25 -> 0.108, 30 -> 0.146, 35 -> 0.201, 40 -> 0.266, 45 -> 0.355, 50 -> 0.408, 55 -> 0.494, 60 -> 0.601, 65 -> 0.706, 70 -> 0.815, 75 -> 0.932, 80 -> 1.057, 85 -> 1.256, 90 -> 1.435, 95 -> 1.573, 100 -> 1.759
*)
(* Ltac2 Eval let f n := 
  let _ := (print_tensorexpr (
    tensor_expr_of_tensor_list
    (hypergraph_to_tensor_list (test_graph n)))) in () in 
  List.iter (fun i => let n := (Int.mul (Int.add 1 i) 5) in 
  printf "%i" n;
  Control.time None (fun () => Notations.do0 (fun () => 10) (fun () =>f n))) (List.range 0 20). *)

(* 
Ltac2 Eval Graph.equal (test_graph 5) (
  tensor_list_to_hypergraph (hypergraph_to_tensor_list (test_graph 5))
). *)

(* Ltac2 Eval 
  Message.print (Graph.print_nice (test_graph 5)).

Ltac2 Eval Message.print (print_tensorlist (
  hypergraph_to_tensor_list (test_graph 5)
)).

Ltac2 Eval Message.print (Graph.print_nice
    (tensor_list_to_hypergraph 
    (hypergraph_to_tensor_list (test_graph 5)))).  *)

(* Set Ltac2 Backtrace.


Ltac2 Set debug_match := true.

(* Ltac2 Eval 
  let m := (mk_match (test_graph 2) (test_graph 2) Int.equal) in
  Message.print (print_sep_list' (Message.concat (fprintf ", ") (Message.break 1 0)) 
    (List.cons m (List.flat_map more (more m))) print_match).
  let _ := try_add_vertex m 0 0 in 
  Message.print (print_match m).
 *)

Ltac2 Eval 
  let m := (mk_match (test_graph 2) (test_graph 2) Int.equal ) in
  let _ := try_add_vertex m 0 0 in 
  Message.print (print_match m).

Ltac2 Eval 
  Message.print (print_tensorlist 
    (hypergraph_to_tensor_list (test_graph 3))).

Ltac2 Eval Message.print (print_int_graph
    (tensor_list_to_hypergraph 
    (hypergraph_to_tensor_list (test_graph 3)))).


Ltac2 Eval hypergraph_to_tensor_list (test_graph 3).

Ltac2 Eval Message.print (print_int_graph
    (tensor_list_to_hypergraph 
    (hypergraph_to_tensor_list (test_graph 5)))).


Ltac2 Eval Message.print (print_tensorlist (
  tensor_expression_to_simplified (
        tensor_expr_of_tensor_list
        (hypergraph_to_tensor_list (test_graph 5))))).


    Ltac2 Eval Message.print (print_tensorexpr (
        tensor_expr_of_tensor_list
        (hypergraph_to_tensor_list (test_graph 5)))).

Ltac2 Eval tensor_expr_of_tensor_list
        (hypergraph_to_tensor_list (test_graph 3)).

Ltac2 Eval 
  let t := _ in 
  let (cs, inner) := extract_contractions t in 
  let (ds, abs) := decompose_contraction_free_expr inner in 
  let abs := List.map_filter parse_abstract abs in 
  mk_tensorlist cs ds abs.

Ltac2 Eval Message.print (print_tensorlist (
  tensor_expression_to_simplified (
        tensor_expr_of_tensor_list
        (hypergraph_to_tensor_list (test_graph 5))))).

Ltac2 Eval Message.print (print_int_graph
    (tensor_list_to_hypergraph 
    (hypergraph_to_tensor_list (test_graph 5)))).

Ltac2 Eval Message.print (print_int_graph
    (tensor_list_to_hypergraph (
      tensor_expression_to_simplified (
        tensor_expr_of_tensor_list
        (hypergraph_to_tensor_list (test_graph 5))
      )

    )
    )).

*)


