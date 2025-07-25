Require Import Ltac2.Init.
Require Import tensorexpression_int.
Require Import FSetExtra.
Require Import hypergraph.


(* Convert a [TensorList] to the corresponding hypergraph. 
  The conversion is, essentially, that contractions become 
  (internal) vertices, abstract tensors become hyperedges,
  deltas become free wires, and any free lower / upper indices
  in the abstract tensors become input / output vertices,
  respectively.

  Vertices are labeled by the [TypeIdx] from the contraction
  or input, while edges are labeled by the [AbsIdx] indexing
  their function. *)
Ltac2 tensor_list_to_hypergraph (t : TensorList) : (TypeIdx, AbsIdx) Graph :=
  (* Start with an empty graph *)
  let g := mk_graph () in 
  (* First, add a vertex for each contraction, recording their indices *)
  let cs_map := List.map (fun (ty, a, b) => 
    let i := add_vertex g (Some ty) None in 
    (i, (ty, a, b))) (t.(contractions)) in 
  (* Then, for each abstract tensor, add a hyperedge, adding vertices for
    each free index, recording them in [in_verts] and [out_verts] as we do
    (they will be marked as appropriately in / out later) *)
  let (in_verts, out_verts, _contr_edges) := (* ([], [], []) *)
    List.fold_right (fun (abs_idx, lower, upper) (ins, outs, contrs) => 
      (* First, get the list of source/lower vertices, adding those we lack *)
      let (new_ins, s) := List.fold_right (fun (ty, a) (ins, s) => (* TODO: Fold left so we can [cons] to [s] rather than appending? *)
        (* Try to find an internal/contraction vertex with the right label, i.e. 
          a contraction with [a] as an _lower_ index (TODO: Check, but I think lower is correct here) *)
        let may_i := List.find_opt (fun (_, (ty', a', _)) =>
          Bool.and (Int.equal ty ty') (Int.equal a a')) cs_map in 
        match may_i with 
        | Some (i, _) => (* Found a matching vertex; add it to the source vertex list *)
          (ins, List.append s [i])
        | None => (* No matching vertex means this is a free index; add it as a vertex marked to be made an input *)
          let i := add_vertex g (Some ty) None in 
          (List.cons i ins, List.append s [i])
        end) lower ([], []) in 
      (* Next, do the same for the target/upper vertices *)
      let (new_outs, t) := List.fold_right (fun (ty, b) (outs, t) => (* TODO: Fold left so we can [cons] to [t] rather than appending? *)
        (* Try to find an internal/contraction vertex with the right label, i.e. 
          a contraction with [b] as an _upper_ index (TODO: Check, but I think upper is correct here) *)
        let may_i := List.find_opt (fun (_, (ty', _, b')) =>
          Bool.and (Int.equal ty ty') (Int.equal b b')) cs_map in 
        match may_i with 
        | Some (i, _) => (* Found a matching vertex; add it to the source vertex list *)
          (outs, List.append t [i])
        | None => (* No matching vertex means this is a free index; add it as a vertex marked to be made an input *)
          let i := add_vertex g (Some ty) None in 
          (List.cons i outs, List.append t [i])
        end) upper ([], []) in
      (* Now, we can add the edge to the graph *) 
      let e := add_edge g s t (Some abs_idx) None in
      (* Finally, record the new input / output vertices we'll need to mark, 
      along with the edge index of this edge *)
      (List.append new_ins ins, List.append new_outs outs, 
        List.cons (e, (abs_idx, lower, upper)) contrs) (* TODO: Remove unused lower / upper values here *)
      ) (t.(abstracts)) ([], [], []) in 
  (* Finally, add a vertex and edge for each delta *)
  let (delta_ins, delta_outs, _delta_es) := List.fold_right 
    (fun (ty, _a, _b) (dins, douts, des) => 
    (* Make input and output vertices *)
    let a_idx := add_vertex g (Some ty) None in 
    let b_idx := add_vertex g (Some ty) None in 
    (* Make an edge for the delta with these as source and target *)
    let e_idx := add_edge g [a_idx] [b_idx] None None in 
    (* Record the new values *)
    (List.append dins [a_idx], List.append douts [b_idx], List.append des [e_idx])
    ) (t.(deltas)) ([], [], []) in 
  (* Now, the graph has all the data we need, and we just need to set 
    the inputs and outputs *)
  set_inputs g (List.append in_verts delta_ins);
  set_outputs g (List.append out_verts delta_outs);
  (* Then our graph is ready! *)
  g.

Import Printf.

(* Construct a [TensorList] from a (restricted form of a) hypergraph: 
  specifically, the only edges that will end up in the [TensorList] 
  are those with non-empty value, which will become AbstractTensors,
  and those with empty value and singleton sources and targets, which
  will become Deltas. We use vertex indices as label indexes. All vertices
  must have (non-empty) values, which are used as their types. *)
Ltac2 hypergraph_to_tensor_list (g : (TypeIdx, AbsIdx) Graph) : TensorList :=
  (* Establish the mapping between indices and types *)
  let vertex_type_map := 
    FMap.mapi (fun v vd => 
    let ty := match vvalue vd with 
    | Some ty => ty 
    | None => printf "WARNING: trying to convert graph to TensorList, but vertex %i has no value (type). Placeholder value -1 will be used" v;
      -1 end in 
    ty) (g.(vdata)) in 
  let vertex_type v := FMap.lookup vertex_type_map v in 
  (* TO DO: Fix this when we properly refactor to understand that upper and 
  lower indices are separate sets, hence can be the same (i.e. einstein 
  notation is valid, up to the lack of contractions Kₐᵃ for each repeated
  label a). For now, this is a nasty hack to make upper and lower indices
  different (simply, lower are even and upper are odd...) *)
  let lower_map v := v in (* Int.lsl v 1 in (* double *) *)
  let upper_map v := v in (* Int.lxor (Int.lsl v 1) 1 in (* double and add 1*) *)
  (* Construct abstract tensors and deltas from the edges *)
  let (abstracts, deltas) := FMap.fold (fun e ed (abs, ds) => 
    (* Look at the value of the edge *)
    match ed.(value) with 
    | None => (* Empty edges must have singleton sources and targets 
      of the same type, in which case they become deltas *)
      if Bool.and (Int.equal (List.length (ed.(s))) 1)
          (Int.equal (List.length (ed.(t))) 1) then 
        (* This is almost a valid delta; test types *)
        let a := List.hd (ed.(s)) in 
        let b := List.hd (ed.(t)) in 
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
    | Some abs_idx => (* Edge has a value, so will become an AbstractTensor *)
      let lower := List.map (fun v => (vertex_type v, lower_map v)) (ed.(s)) in 
      let upper := List.map (fun v => (vertex_type v, upper_map v)) (ed.(t)) in 
      (List.cons (abs_idx, lower, upper) abs, ds)
    end)
  (g.(edata)) ([], []) in 
  
  (* Now, we use the internal vertices to make our contractions *)
  let contractions := FMap.fold (fun v _vd cs => 
    if is_boundary g v then 
      (* Boundary vertex; do nothing *)
      cs else
    (* Internal vertex; this becomes a contraction *)
    let ty := vertex_type v in 
    List.cons (ty, lower_map v, upper_map v) cs
    ) (g.(vdata)) [] in 
  
  (* Finally, we have all our data *)
  mk_tensorlist contractions deltas abstracts.




Import Printing.

Ltac2 test_graph (ub : int) : (TypeIdx, AbsIdx) Graph :=
  let g := mk_graph () in 
  let rnge := List.range 0 ub in 
  let _verts := List.map (fun i => 
    add_vertex g (Some (Int.div i 2)) None) rnge in
  let _edges := List.map (fun i => 
    add_edge g (List.firstn i rnge) (List.skipn i rnge) (Some i) None) rnge in
  g.

Ltac2 test_tensorlist (ub : int) : TensorList :=
  hypergraph_to_tensor_list (test_graph ub).

Ltac2 test_tensorexpr (ub : int) : TensorExpr :=
  tensor_expr_of_tensor_list (hypergraph_to_tensor_list (test_graph ub)).

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



(* Ltac2 Eval 
  Message.print (print_int_graph (test_graph 5)).

Ltac2 Eval Message.print (print_int_graph
    (tensor_list_to_hypergraph 
    (hypergraph_to_tensor_list (test_graph 5)))). *)

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


