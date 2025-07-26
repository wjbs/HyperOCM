Require Import Ltac2.Init.
Require Import tensorexpression.
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


Import Printf.

(* Convert a [TensorList] to the corresponding hypergraph. 
  The conversion is, essentially, that contractions become 
  (internal) vertices, abstract tensors become hyperedges,
  deltas become free wires, and any free lower / upper indices
  in the abstract tensors become input / output vertices,
  respectively.

  Vertices are labeled by the [TypeIdx] from the contraction
  or input, while edges are labeled by the [AbsIdx] indexing
  their function.
  
  The inputs and outputs of the graph are given as lists
  of the registers (which should be free in the [TensorList])
  which should be the inputs and outputs of the graph. 
  
  Returns the generated graph, the mapping from registers
  to vertices, and the map from abtract tensors to edges
  (with abstract tensors here represented by their indices 
  in the [TensorList]'s list of abstract tensors).
  
  Note that the sums of the [TensorList] must be unique; 
  if they are not, the graph _may_ be correct but the
  returned maps will not. *)
Ltac2 tensor_list_to_hypergraph (t : TensorList) 
  (inputs : TypedVar list) (outputs : TypedVar list) : 
  Graph.t * 
  (TypeIdx, VarIdx, int) FMap2.t * 
  (int, int) FMap.t :=
  let of_ty (t : TypeIdx) : string option := 
    if String.equal t "" then None else Some t in 
  (* Start with an empty graph *)
  let g := Graph.make () in 

  (* First, add a vertex for each sum / bound register, 
    recording their indices in the map which will record 
    the vertex indices of registers *)
  let (g, reg_vtx_map) := List.fold_left (fun (g, reg_vtx_map) (ty, var) => 
    (* Note that using fold_left means that sum shadowing will behave properly;
    the innermost summation will be the one whose vertex edges connect to 
    (though as their vertices are interchangeable, this is somewhat irrelevant) *)
    (* printf "Looking at sum ∑ %s : %s" var ty; *)
    let (g, idx) := Graph.add_vertex (of_ty ty) None g in 
    g, FMap2.add ty var idx reg_vtx_map) (g, FMap2.empty string_tag string_tag) 
      (t.(sums)) in

  (* Then, for each free register of the [TensorList], add a vertex *)
  let (g, reg_vtx_map) := FSet2.fold (fun ty var (g, reg_vtx_map) =>
    let (g, idx) := Graph.add_vertex (of_ty ty) None g in 
    g, FMap2.add ty var idx reg_vtx_map) 
    (tensorlist_free_set t) (g, reg_vtx_map) in 

  
  (* Make sure every input and output has been added as a vertex, 
    adding those that haven't. TODO: Should we actually do the latter, 
    or would that be invalid? *)
  let (g, reg_vtx_map) := List.fold_right (fun (ty, var) (g, reg_vtx_map) => 
    match FMap2.find_opt ty var reg_vtx_map with
    | Some _ => 
      (* Added; do nothing *)
      (g, reg_vtx_map)
    | None => 
      (* Add the missing vertex*)
      let (g, idx) := Graph.add_vertex (of_ty ty) None g in 
      (g, FMap2.add ty var idx reg_vtx_map)
    end) (List.append inputs outputs) (g, reg_vtx_map) in 
  

  (* Wrap the mapping from registers to vertices in a lookup function 
    with a useful error message *)
  let idx_of_reg ((ty, var) : TypedVar) : int :=
    match FMap2.find_opt ty var reg_vtx_map with  
    | Some idx => idx
    | None => Control.throw (Tactic_failure (Some 
      (Message.of_string (String.concat "" ["tensor_list_to_hypergraph ";
        "tried to lookup the vertex index corresponding to register ";
        "("; var; " : "; ty; ") "; "but a corresponding vertex has not ";
        "been added. This should never happen and is a bug; please report."
        ]))))
    end in 

  (* For each abstract tensor, add a hyperedge with source and target 
    corresponding to the lower/input and upper/output registers, respectively *)
  let (g, edge_map) := List.fold_right 
    (fun (abs_idx, (name, lower, upper)) (g, edge_map) => 
    let s := List.map idx_of_reg lower in 
    let t := List.map idx_of_reg upper in 
    let (g, e_idx) := Graph.add_edge (of_ty name) None s t g in 
    (* Return the updated graph and map *)
    (g, FMap.add abs_idx e_idx edge_map)) 
    (List.enumerate (t.(abstracts))) (g, FMap.empty FSet.Tags.int_tag) in 

  
  (* Finally, set the inputs and outputs of the graph: *)
  let g := Graph.set_inputs (List.map idx_of_reg inputs) g in 
  let g := Graph.set_outputs (List.map idx_of_reg outputs) g in 

  (g, reg_vtx_map, edge_map).


Import Printf.


(* Helper to sort a list of (int * _) by first component *)
Local Ltac2 sort_list_fst_int (l : (int * 'a) list) : (int * 'a) list :=
  List.sort (fun (i, _) (j, _) => Int.compare i j) l.


(* Construct a [TensorList] from a hypergraph. The conversion is that
  vertices become sums and hyperedges become abstract tensors. 

  Takes a mapping from vertex indices to names to name the variables. 
  If an index is not named, its name is taken to be its type 
  concatenated with its index.

  Returns the [TensorList], the lists of inputs and outputs registers
  corresponding to those of the graph, the mapping from internal vertices
  to sums, and the mapping from hyperedges to abstract tensors (the latter 
  two in terms of their indices in the lists of sums and abstract 
  tensors, respectively). *)
Ltac2 hypergraph_to_tensor_list (g : Graph.t) 
  (vtx_names : (int, VarIdx) FMap.t) : 
  TensorList * TypedVar list * TypedVar list 
  * (int, int) FMap.t * (int, int) FMap.t :=

  (* First, determine the registers corresponding to each vertex *)
  let idx_reg_map := FMap.mapi (fun v vd => 
    let ty := VData.value vd in 
    let name := match FMap.find_opt v vtx_names with 
      | Some name => name
      | None => String.app ty (string_of_int v)
      end in 
    (ty, name)) (Graph.vdata g) in 

  (* Wrap the naming map in a lookup function, with an error message *)
  let vertex_reg v := match FMap.find_opt v idx_reg_map with
    | Some ty => ty
    | None => printf "ERROR: while trying to convert graph to TensorList, tried to find type of vertex %i, but this vertex does not seem to appear in the graph." v;
      Control.throw (Not_found)
    end in 

  (* Construct the abstract tensors of the [TensorList], recording 
    the indices of each edge *)
  let (abs, edge_map) := List.fold_right (fun (idx, (e, ed)) (abs, edge_map) => 
    let lower := List.map vertex_reg (EData.source ed) in 
    let upper := List.map vertex_reg (EData.target ed) in 
    let name := EData.value ed in 
    (* Add the abstract tensor, and record the index correspondence *)
    ((name, lower, upper) :: abs, FMap.add e idx edge_map)
    ) (List.enumerate (sort_list_fst_int (FMap.bindings (Graph.edata g))))
    ([], FMap.empty FSet.Tags.int_tag) in 

  (* Finally, determine the sums from the internal vertices *)
  let internal_vertices := 
    List.filter_out (Graph.is_boundary g) (Graph.vertices g) in 
  let (sums, vertex_map) := List.fold_right 
    (fun (idx, v) (sums, vertex_map) => 
    (vertex_reg v :: sums, FMap.add v idx vertex_map))
    (List.enumerate (List.sort Int.compare internal_vertices))
    ([], FMap.empty FSet.Tags.int_tag) in 
  

  (* Compute the input and output lists in terms of registers *)
  let inputs' := List.map vertex_reg (Graph.inputs g) in 
  let outputs' := List.map vertex_reg (Graph.outputs g) in 

  (* Finally, put together the [TensorList] and return the other data *)
  {sums := sums; abstracts := abs}, inputs', outputs', vertex_map, edge_map.

  
Module Testing.

Import hypercaml_testing.caml_test_graphs.

Import Printing.

Ltac2 roundtrip_graph (g : Graph.t) : Graph.t :=
  let (tl, ins, outs, _vert_map, _edge_map) := 
    hypergraph_to_tensor_list g (FMap.empty FSet.Tags.int_tag) in 
  let (g', _regmap, _absmap) := tensor_list_to_hypergraph tl ins outs in 
  g'.

Ltac2 print_graph (g : Graph.t) : unit :=
  Message.print (Graph.print_nice g).

Ltac2 print_match (m : Match.t) : unit :=
  print (Match.print_nice m).

Ltac2 print_match_full (m : Match.t) : unit :=
  print (Match.print_nice_full m).

Ltac2 pr_tensor_of_graph (g : Graph.t) : message :=
  let (tl, _ins, _outs, _, _) := 
    hypergraph_to_tensor_list g (FMap.empty FSet.Tags.int_tag) in 
  pr_tensorlist tl.

Ltac2 print_tensor_of_graph (g : Graph.t) : unit :=
  print (pr_tensor_of_graph g).


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


Ltac2 test_simple_graph () : UTest.t :=
  UTest.foreach ["";"f";"g"] (fun name => test_roundtrip_iso
  (String.app "simple graph with edge value/type " name)
  (make_simple_graph name)).

Ltac2 test_cycle_graph () : UTest.t :=
  test_roundtrip_iso
  ("cycle graph of size 3")
  (make_cycle_graph ()).

Ltac2 test_path_graph () : UTest.t :=
  let types := ["a"; ""; "b"; "a"; "a"] in 
  test_roundtrip_iso
  (String.app "path graph with vertex types "
    (String.concat ", " types))
  (make_path_graph types).

Ltac2 test_scalar_graph () : UTest.t :=
  test_roundtrip_iso
  "scalar graph"
  (make_scalar_graph ()).

Ltac2 test_star_graph () : UTest.t :=
  test_roundtrip_iso
  "star graph"
  (make_star_graph "center" ["leaf1"; "leaf2"; "leaf1"; "leaf1"; "leaf3"]).

Ltac2 test_hgraph () : UTest.t :=
  test_roundtrip_iso
  "hgraph"
  (make_hgraph ()).

Ltac2 test_hgraph2 () : UTest.t :=
  test_roundtrip_iso
  "hgraph2"
  (make_hgraph2 ()).

Ltac2 test_boundary_graph () : UTest.t :=
  test_roundtrip_iso
  "boundary graph"
  (make_boundary_graph ()).

Ltac2 tensor_tests () := [
  ("simple_graph_roundtrip", test_simple_graph);
  ("cycle_graph_roundtrip", test_cycle_graph);
  ("path_graph_roundtrip", test_path_graph);
  ("scalar_graph_roundtrip", test_scalar_graph);
  ("star_graph_roundtrip", test_star_graph);
  ("hgraph_roundtrip", test_hgraph);
  ("hgraph2_roundtrip", test_hgraph2);
  ("boundary_graph_roundtrip", test_boundary_graph)
].

Ltac2 Eval UTest.asserts UTest.noprint (tensor_tests ()).


End Testing.










(* Given a list of values and a sublist thereof, computes a 
  permutation function such that reordering the list by that 
  permutation exposes the sublist as an intial segment. 
  Works only with non-duplicate lists.

  For example, if [l] is a list of which [subl] is sublist, 
  meaning every element of [subl] appears in [l], then if 
  [f := bring_to_front_perm l subl], the list 
  [List.map (fun (i, _) => List.nth l (f i)) (List.enumerate l)]
  will look like [subl ++ rest] for some list [rest]. 
  
  This function is uniquely defined by the property that this 
  list [rest] will have its elements in the same relative order
  as those of [l]. *)
Ltac2 bring_to_front_perm (eq : 'a -> 'a -> bool) 
  (l : 'a list) (subl : 'a list) : int -> int :=
  let len_l := List.length l in 
  let enum_l := List.enumerate l in 
  let mem_subl e := List.mem eq e subl in 
  let len_subl := List.length subl in
  (* The list of length [len_l] whose elements record how many 
    elements _not_ in [subl] occur in [l] up to and including that index *) 
  let (non_subl_counts, _) := 
    List.fold_left (fun (acc, count) e => 
      let new_count := if Bool.neg (mem_subl e) then Int.add count 1 else count in
      (List.append acc [new_count], new_count)) ([], 0) l in
  let enum_non_subl_counts := List.enumerate non_subl_counts in 
  fun k => 
  (* There are two cases. If we are in the inital segment that should
    become [subl], we just need to find the index of that element of
    [subl]. If we are past this initial segment, we need to find the
    appropriate _non-[subl]-element_ of [l]. *)
  (* First, basic bounds: *)
  if Bool.or (Int.lt k 0) (Int.le len_l k) then k else
  (* Now, the main case split: *)
  if Int.lt k len_subl then
    (* Case 1: initial subl segment *)
    (* This is the element we want [nth <result> k] to be: *)
    let elem := List.nth subl k in 
    (* Find its index in [l] *)
    let (i, _) := List.find (fun (_, elem') => eq elem elem') enum_l in 
    (* This is the index we need *)
    i
  else 
    (* Case 2: past the [subl] intial segment *)
    (* We need to answer 'What is the smallest index at which 
      we will have [k+1 - len_subl] non-elements of [subl] behind or at us'. 
      This is answered by the index of the first element of 
      [non_subl_counts] equal to [k+1-len_subl] *)
    let k' := Int.sub (Int.add k 1) len_subl in 
    fst (List.find (fun (_, count) => Int.equal count k') enum_non_subl_counts).



(* Given a list of values and a sublist thereof, computes a 
  permutation function such that reordering the list by that 
  permutation exposes the sublist as a terminal segment. 
  Works only with non-duplicate lists.

  For example, if [l] is a list of which [subl] is sublist, 
  meaning every element of [subl] appears in [l], then if 
  [f := send_to_back_perm l subl], the list 
  [List.map (fun (i, _) => List.nth l (f i)) (List.enumerate l)]
  will look like [rest ++ subl] for some list [rest]. 
  
  This function is uniquely defined by the property that this 
  list [rest] will have its elements in the same relative order
  as those of [l]. *)
Ltac2 send_to_back_perm (eq : 'a -> 'a -> bool) 
  (l : 'a list) (subl : 'a list) : int -> int :=
  let len_l := List.length l in 
  let enum_l := List.enumerate l in 
  let mem_subl e := List.mem eq e subl in 
  let len_subl := List.length subl in
  (* The list of length [len_l] whose elements record how many 
    elements _not_ in [subl] occur in [l] up to and including that index *) 
  let (non_subl_counts, _) := 
    List.fold_left (fun (acc, count) e => 
      let new_count := if Bool.neg (mem_subl e) then Int.add count 1 else count in
      (List.append acc [new_count], new_count)) ([], 0) l in
  let enum_non_subl_counts := List.enumerate non_subl_counts in 
  fun k => 
  (* There are two cases. If we are in the terminal segment that should
    become [subl], we just need to find the index of that element of
    [subl]. If we are before this terminal segment, we need to find the
    appropriate _non-[subl]-element_ of [l]. *)
  (* First, basic bounds: *)
  if Bool.or (Int.lt k 0) (Int.le len_l k) then k else
  (* Now, the main case split: *)
  if Int.lt k (Int.sub len_l len_subl) then
    (* Case 1: before terminal subl segment *)
    (* We need to answer 'What is the smallest index at which 
      we will have [k+1] non-elements of [subl] behind or at us'. 
      This is answered by the index of the first element of 
      [non_subl_counts] equal to [k+1] *)
    fst (List.find (fun (_, count) => Int.equal count (Int.add k 1)) enum_non_subl_counts)
  else 
    (* Case 2: terminal [subl]  segment *)
    (* This is the element we want [nth <result> k] to be: *)
    let elem := List.nth subl (Int.sub k (Int.sub len_l len_subl)) in 
    (* Find its index in [l] *)
    let (i, _) := List.find (fun (_, elem') => eq elem elem') enum_l in 
    (* This is the index we need *)
    i.




(* Remove the _first_ element of a list satisfying a given predicate. 
  If none is found, return None. *)
Ltac2 rec remove_first (f : 'a -> bool) (l : 'a list) : 'a list option :=
  match l with 
  | [] => None
  | a :: l' => if f a then Some l' 
    else Option.map (fun r => a :: r) (remove_first f l')
  end.

(* Test if two list are equal up to permutation. Assumes the 
  given equality is an equivalence relation. *)
Ltac2 rec perm_eq (eq : 'a -> 'a -> bool) (l : 'a list) (l' : 'a list) : bool :=
  match l with 
  | [] => List.is_empty l'
  | a :: l_rest => match remove_first (eq a) l' with 
    | None => false
    | Some l'_rest => perm_eq eq l_rest l'_rest
    end
  end.

(* Permute a list by a permutation of the indices. If a given index 
  is mapped outside the length of the list, its initial value is used. *)
Ltac2 permute_list (f : int -> int) (l : 'a list) :=
  List.map (fun (i, v) => Option.default v (List.nth_opt l (f i)))
    (List.enumerate l).

(* Permute a list by the inverse of a permutation of the indices. 
  (Strictly, works more generally for an injective funciton, not 
  just permutation, ordering the elements of the list by the 
  relative ordering of the funciton outputs.) *)
Ltac2 inv_permute_list (f : int -> int) (l : 'a list) :=
  List.map fst (List.sort (fun (i, _) (j, _) => Int.compare i j)
    (List.map (fun (i, v) => (f i, v)) (List.enumerate l))).

(* TODO: Test permute_list and inv_permute_list *)


(* Given a list and a sublist thereof, removes the sublist from the
  list. Here, sublist means in the sense of multisets, so duplicates
  are allowed and count separately. Returns None if the sublist is
  not actualyl a sublist of the list. *)
Ltac2 remove_sublist_opt (eq : 'a -> 'a -> bool) 
  (l : 'a list) (subl : 'a list) : 'a list option :=
  let rec go l subl :=
    match l with 
    | [] => if List.is_empty subl then Some [] else None
    | a :: l' => match remove_first (eq a) subl with 
      | Some subl' => (* There was an [a] in [subl] *)
        go l' subl'
      | None => (* [a] was not in [subl] *)
        Option.map (List.cons a) (go l' subl)
      end
    end in
  go l subl.

(* Given a list and a sublist thereof, removes the sublist from the
  list. Here, sublist means in the sense of multisets, so duplicates
  are allowed and count separately. Raises an [Invalid_argument] 
  exception if the sublist is not actually a sublist of the list. *)
Ltac2 remove_sublist (eq : 'a -> 'a -> bool) 
  (l : 'a list) (subl : 'a list) : 'a list :=
  match remove_sublist_opt eq l subl with 
  | Some l' => l'
  | None =>
    Control.throw_invalid_argument "subl is not a sublist of l (in remove_sublist)"
  end.


(* Given a list and a sublist thereof, return the permutation of
  the original list with the sublist as an initial segment. Raises
  an [Invalid_argument] error if the sublist is not a sublist of
  the original list.
  
  Literally, concatenates [subl] and [remove_sublist eq l subl]. *)
Ltac2 bring_to_front (eq : 'a -> 'a -> bool) 
  (l : 'a list) (subl : 'a list) : 'a list :=
  match remove_sublist_opt eq l subl with 
  | Some l' => List.append subl l'
  | None => 
    Control.throw_invalid_argument "subl is not a sublist of l (in bring_to_front)"
  end.


(* Given a list and a sublist thereof, return the permutation of
  the original list with the sublist as a terminal segment. Raises
  an [Invalid_argument] error if the sublist is not a sublist of
  the original list.
  
  Literally, concatenates [subl] and [remove_sublist eq l subl]. *)
Ltac2 send_to_back (eq : 'a -> 'a -> bool) 
  (l : 'a list) (subl : 'a list) : 'a list :=
  match remove_sublist_opt eq l subl with 
  | Some l' => List.append l' subl
  | None => 
    Control.throw_invalid_argument "subl is not a sublist of l (in send_to_back)"
  end.


Module PermTesting. 

Import PrintingExtra.

(* Test that two lists are equal to each other, up to permutation. *)
Ltac2 test_is_perm_pr (eq : 'a -> 'a -> bool) (pr : 'a -> message)
  (on_err : string) (expected : 'a list) (test_val : 'a list) : UTest.t :=
  UTest.value_eq_pr (perm_eq eq) (of_list pr) 
    (fun()=>expected) (fun()=>test_val)
    (String.app "lists should have been permutations. Message: " on_err).


(* Helpers for permutation function tests*)

Ltac2 test_bring_to_front_perm_on (l : int list) (subl : int list) : UTest.t :=
  let len_l := List.length l in let len_subl := List.length subl in 
  let l' := permute_list (bring_to_front_perm Int.equal l subl) l in 
  UTest.seq 
    (UTest.value_eqv_pr (List.equal Int.equal) (of_list of_int)
      (String.concat "" ["First "; string_of_int len_l; 
        " elements should be the sublist"]) 
      (subl)
      (List.firstn len_subl l'))
    (test_is_perm_pr Int.equal of_int 
    "bring_to_front_perm should have been a permutation" l l').

Ltac2 test_bring_to_front_perm_on' (l, subl) :=
  test_bring_to_front_perm_on l subl.

Ltac2 test_send_to_back_perm_on (l : int list) (subl : int list) : UTest.t :=
  let len_l := List.length l in let len_subl := List.length subl in 
  let l' := permute_list (send_to_back_perm Int.equal l subl) l in 
  UTest.seq 
    (UTest.value_eqv_pr (List.equal Int.equal) (of_list of_int)
      (String.concat "" ["Last "; string_of_int len_l; 
        " elements should be the sublist"]) 
      (subl)
      (List.lastn len_subl l'))
    (test_is_perm_pr Int.equal of_int 
    "send_to_back_perm should have been a permutation" l l').

Ltac2 test_send_to_back_perm_on' (l, subl) :=
  test_send_to_back_perm_on l subl.


(* Helpers for list permutation tests *)

Ltac2 test_bring_to_front_on (l : int list) (subl : int list) : UTest.t :=
  let len_l := List.length l in let len_subl := List.length subl in 
  let l' := bring_to_front Int.equal l subl in 
  UTest.seq 
    (UTest.value_eqv_pr (List.equal Int.equal) (of_list of_int)
      (String.concat "" ["First "; string_of_int len_l; 
        " elements should be the sublist"]) 
      (subl)
      (List.firstn len_subl l'))
    (test_is_perm_pr Int.equal of_int 
    "bring_to_front should have been a permutation" l l').

Ltac2 test_bring_to_front_on' (l, subl) : UTest.t :=
  test_bring_to_front_on l subl.

Ltac2 test_send_to_back_on (l : int list) (subl : int list) : UTest.t :=
  let len_l := List.length l in let len_subl := List.length subl in 
  let l' := send_to_back Int.equal l subl in 
  UTest.seq 
    (UTest.value_eqv_pr (List.equal Int.equal) (of_list of_int)
      (String.concat "" ["Last "; string_of_int len_l; 
        " elements should be the sublist"]) 
      (subl)
      (List.lastn len_subl l'))
    (test_is_perm_pr Int.equal of_int 
    "send_to_back should have been a permutation" l l').

Ltac2 test_send_to_back_on' (l, subl) :=
  test_send_to_back_on l subl.



Ltac2 test_remove_sublist_opt_Some 
  ((l, subl) : int list * int list) : UTest.t := 
  let len_l := List.length l in let len_subl := List.length subl in 
  let opt_l' := remove_sublist_opt Int.equal l subl in 
  UTest.seqs [
    UTest.opt_is_some_pr (of_list of_int)
      "remove_sublist_opt should succeed" opt_l';
    match opt_l' with 
    | None => (* The above will fail already; we can skip the rest *)
      UTest.notest ()
    | Some l' => UTest.seqs [
    UTest.int_eqv 
      "length of remove_sublist_opt should be difference of list lengths"
      (Int.sub len_l len_subl)
      (List.length l');
    test_is_perm_pr Int.equal of_int 
    "remove_sublist_opt should give a permutation when subl is concatted" 
    l (List.append subl l')]
    end].

Ltac2 test_remove_sublist_opt_None
  ((l, subl) : int list * int list) : UTest.t := 
  let opt_l' := remove_sublist_opt Int.equal l subl in 
  UTest.opt_is_none_pr (of_list of_int) 
    (String.concat "" [
      "remove_sublist_opt should return None for non-sublists ";
      "(l = "; to_string (of_list of_int l); ", subl = ";
        to_string (of_list of_int l)])
    opt_l'.


(* Values on which to test these functions *)

Ltac2 _subset_lists () :=
  [ 
    ([1; 2; 3; 4; 5], [1; 2; 3]);
    ([1; 2; 3; 4; 5], [2; 3; 4]);
    ([1; 2; 3; 4; 5], [1; 4]);
    ([1; 2; 3; 4; 5], [3; 5]);
    ([1; 2; 3; 4; 5], [1]);
    ([1; 2; 3; 4; 5], [])
  ].

Ltac2 _non_subset_sublists () :=
  [
    ([1; 1; 2; 2; 4; 5], [1; 2; 2; 5]);
    ([1; 1; 2; 2; 4; 5], [4; 2; 1; 1])
  ].

Ltac2 _all_sublists () :=
  List.append (_subset_lists()) (_non_subset_sublists()).

Ltac2 _non_sublists () :=
  [
    ([1; 1; 2; 2; 4; 5], [1; 2; 2; 2]); (* Too many 2's *)
    ([1; 1; 2; 2; 4; 5], [4; 2; 1; 3]) (* No 3 in first *)
  ].




Ltac2 test_bring_to_front_perm () :=
  UTest.foreach (_subset_lists())
    test_bring_to_front_perm_on'.

Ltac2 test_send_to_back_perm () :=
  UTest.foreach (_subset_lists())
    test_send_to_back_perm_on'.

Ltac2 test_bring_to_front () :=
  UTest.foreach
    (_all_sublists())
    test_bring_to_front_on'.

Ltac2 test_send_to_back () :=
  UTest.foreach
    (_all_sublists())
    test_send_to_back_on'.

Ltac2 test_remove_sublist_opt_success () :=
  UTest.foreach (_all_sublists())
    test_remove_sublist_opt_Some.

Ltac2 test_remove_sublist_opt_failure () :=
  UTest.foreach (_non_sublists())
    test_remove_sublist_opt_None.

Ltac2 tests () := [
  ("bring_to_front_perm success", test_bring_to_front_perm);
  ("send_to_back_perm success", test_send_to_back_perm);
  ("remove_sublist_opt success", test_remove_sublist_opt_success);
  ("remove_sublist_opt failure", test_remove_sublist_opt_failure);
  ("bring_to_front success", test_bring_to_front);
  ("send_to_back success", test_send_to_back)
].

Ltac2 Eval UTest.asserts UTest.noprint (tests()).

End PermTesting.







