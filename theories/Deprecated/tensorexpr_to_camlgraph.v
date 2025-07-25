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



