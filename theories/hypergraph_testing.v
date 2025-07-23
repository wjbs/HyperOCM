Require HypercamlInterface.
Require hypergraph.
Require hypergraph_compat.

Import Ltac2.Init.



Module UTest.

(* A test is a function taking printers for info, warnings, and errors
  which returns a boolean *)
Ltac2 Type t := 
    (message -> unit) -> (* Info printer *)
    (message -> unit) -> (* Warning printer *)
    (message -> unit) -> (* Error printer *)
    (unit -> bool).



Ltac2 pr_with_prefix (m : message) : message -> unit :=
  fun m' => 
  Message.print (Message.concat 
  (Message.concat m (Message.break 1 0)) m').

Ltac2 pr_info m := 
  pr_with_prefix (Message.of_string "[INFO]") m.
Ltac2 pr_warn m := 
  pr_with_prefix (Message.of_string "[WARNING]") m.
Ltac2 pr_err m := 
  pr_with_prefix (Message.of_string "[ERROR]") m.

Ltac2 noprint (_ : message) : unit := ().

(* FIXME: Move *)
Ltac2 of_bool (b : bool) : message :=
  match b with 
  | true => Message.of_string "true"
  | false => Message.of_string "false"
  end.
(* FIXME: Move *)
Ltac2 of_list (pr : 'a -> message) : 'a list -> message := fun l => 
  Message.concat (Message.concat 
  (Message.of_string "[")
  (hypergraph.GraphPrinting.print_sep_list' 
    (Message.of_string ", ") l pr))
  (Message.of_string "]").

(* Run a test, printing all messages as-is *)
Ltac2 run_raw (test : unit -> t) : bool :=
  test () Message.print Message.print Message.print ().

(* Run a test, printing all messages with prefixes indicating their type *)
Ltac2 run (test : unit -> t) : bool :=
  test () pr_info pr_warn pr_err ().

(* Run a test, printing any warnings and errors but no info *)
Ltac2 check (test : unit -> t) : bool :=
  test ()
    noprint 
    pr_warn
    pr_err
    ().

(* Run a test, printing only errors and throwing a fatal exception 
  if the result is false*)
Ltac2 assert (test : unit -> t) : unit :=
  match test () noprint noprint pr_err () with
  | true => ()
  | false => Control.throw Assertion_failure
  end.

(* Versions of running a test for lists of labeled tests *)

Ltac2 run_raws (tests : (string * (unit -> t)) list) : bool :=
  List.fold_left (fun b (name, t) => 
  pr_info (Message.of_string (String.app "Running test: " name));
  Bool.and (run_raw t) b) true tests.

Ltac2 runs (tests : (string * (unit -> t)) list) : bool :=
  List.fold_left (fun b (name, t) => 
  pr_info (Message.of_string (String.app "Running test: " name));
  Bool.and (run t) b) true tests.

Ltac2 checks (tests : (string * (unit -> t)) list) : bool :=
  List.fold_left (fun b (name, t) => 
  pr_info (Message.of_string (String.app "Running test: " name));
  Bool.and (check t) b) true tests.

Ltac2 asserts (pr_run : message -> unit) 
  (tests : (string * (unit -> t)) list) : unit :=
  List.iter (fun (name, t) => 
  pr_run (Message.of_string (String.app "Running test: " name));
  assert t) tests.

(** Common assertion constructors *)

Ltac2 notest () : t :=
  fun _info _warn _err () => true.

Ltac2 seq : t -> t -> t := fun test1 test2 => 
  fun info warn err () => 
  Bool.and (test1 info warn err ()) (test2 info warn err ()).

Ltac2 seqs : t list -> t := fun tests => 
  List.fold_right seq tests (notest ()).

(* Returns the boolean value, printing the message if the value is false *)
Ltac2 with_err (pr : message -> unit) (m : message) (b : bool) : bool :=
  match b with 
  | true => true
  | false => pr m; false
  end.

(* Returns the boolean value, printing the string if the value is false *)
Ltac2 with_errs (pr : message -> unit) (s : string) (b : bool) : bool :=
  match b with 
  | true => true
  | false => pr (Message.of_string s); false
  end.

(* Tests two values for equality, using a printer for better info/error messages *)
Ltac2 value_eq_pr (eq : 'a -> 'a -> bool) (pr : 'a -> message)
  (expected : unit -> 'a) (test_val : unit -> 'a) (on_err : string) : t :=
  fun info _warn err () => 
  let ev := expected () in 
  info (Message.concat (Message.of_string "Expected value: ") (pr ev));
  let v := test_val () in 
  info (Message.concat (Message.of_string "Actual value:   ") (pr v));
  let res := eq ev v in 
  let base_err_msg := Message.concat (Message.concat (Message.concat 
    (Message.of_string "Values did not match! Expected ")
    (pr ev))
    (Message.of_string ", got "))
    (pr v) in
  let err_msg := Message.concat (Message.concat 
    base_err_msg 
    (Message.of_string ". Message: "))
    (Message.of_string on_err) in
  with_err err err_msg res.

(* Tests two values for equality *)
Ltac2 value_eq (eq : 'a -> 'a -> bool)
  (expected : unit -> 'a) (test_val : unit -> 'a) (on_err : string) : t :=
  fun _info _warn err () => 
  let ev := expected () in 
  let v := test_val () in 
  let res := eq ev v in 
  let err_msg := Message.concat 
    (Message.of_string "Values did not match! Message: ")
    (Message.of_string on_err) in
  with_err err err_msg res.

(* Tests two ints for equality *)
Ltac2 int_eq 
  (on_err : string)
  (expected : unit -> int) (test_val : unit -> int) : t :=
  value_eq_pr Int.equal Message.of_int test_val expected on_err.

(* Tests two bools for equality *)
Ltac2 bool_eq 
  (on_err : string)
  (expected : unit -> bool) (test_val : unit -> bool) : t :=
  value_eq_pr Bool.equal of_bool test_val expected on_err.

(* Tests two strings for equality *)
Ltac2 string_eq 
  (on_err : string)
  (expected : unit -> string) (test_val : unit -> string) : t :=
  value_eq_pr String.equal Message.of_string test_val expected on_err.

(* Tests two lists of ints for equality *)
Ltac2 int_list_eq 
  (on_err : string)
  (expected : unit -> int list) (test_val : unit -> int list) : t :=
  value_eq_pr (List.equal Int.equal)
  (of_list Message.of_int) test_val expected on_err.

(* Tests two unthunked ints for equality *)
Ltac2 int_eqv 
  (on_err : string)
  (expected : int) (test_val : int) : t :=
  value_eq_pr Int.equal Message.of_int 
    (fun () => test_val) (fun () => expected) on_err.

(* Tests two unthunked bools for equality *)
Ltac2 bool_eqv 
  (on_err : string)
  (expected : bool) (test_val : bool) : t :=
  value_eq_pr Bool.equal of_bool 
    (fun () => test_val) (fun () => expected) on_err.

(* Tests two unthunked strings for equality *)
Ltac2 string_eqv 
  (on_err : string)
  (expected : string) (test_val : string) : t :=
  value_eq_pr String.equal Message.of_string 
  (fun () => test_val) (fun () => expected) on_err.

(* Tests two unthunked lists of ints for equality *)
Ltac2 int_list_eqv 
  (on_err : string)
  (expected : int list) (test_val : int list) : t :=
  value_eq_pr (List.equal Int.equal)
  (of_list Message.of_int) 
  (fun () => test_val) (fun () => expected) on_err.

Ltac2 example () : t := 
  bool_eq "Equality should be reflexive" 
    (fun () => true) (fun () => true).
Ltac2 examplev () : t := 
  bool_eqv "Equality should be reflexive" true true.

End UTest.



Module caml_test_graphs.

Import HypercamlInterface.

(* Warning! This function will fail on bad inputs! *)
Ltac2 graph_of_edges_in_out 
  (es : (string * int option * int list * int list) list) 
  (ins : int list) (outs : int list)
  (extra_verts : int list) : Graph.t :=
  (* Get all mentioned vertices *)
  let vertices := List.nodup Int.equal (
    List.concat [List.flat_map (fun (_, _, s, t) => List.append s t) es;
    ins; outs; extra_verts]) in
  let g := Graph.make () in 
  (* Add all vertices to the graph *)
  let g := List.fold_right 
    (fun vi g => fst (Graph.add_vertex None (Some vi) g)) vertices g in 
  (* Add all edges to the graph *)
  let g := List.fold_right
    (fun (i, (value, idx, s, t)) g => 
      fst (Graph.add_edge (Some value) (Some (Option.default i idx)) s t g)) 
    (List.enumerate es) g in 
  Graph.set_outputs outs (Graph.set_inputs ins g).
  
Ltac2 Notation 
  "!Graph" ins(list0(tactic(0), ",")) "->" outs(list0(tactic(0), ",")) ":"
    edges(list0( (* A list of edges, each of which look like... *)
      seq(opt(seq(ident, opt(seq("(", tactic(0), ")")), ":")), 
        (* ... an optional name for the edge, such as "f :", with itself 
          an optional edge index, e.g. "f (2) :", or nothing... *)
      list0(tactic(0), ","), (* ... a comma-separated list of input vertices ... *)
      "->",
      list0(tactic(0), ",") (* ... and a comma-separated list of output vertices. *)
      ), ";"))
    verts(opt(seq("and", list1(tactic(0), ",")))) : 2 :=
  let edges' := List.map (fun (may_id_idx, s, t) : 
    (string * int option * int list * int list) => 
    let (name, may_idx) := Option.map_default 
      (fun (name, may_idx) => (Ident.to_string name, may_idx)) 
        ("", None) may_id_idx in
    (name, may_idx, s, t)) edges in 
  let extra_verts : int list := Option.default [] verts in 
  graph_of_edges_in_out edges' ins outs extra_verts.


(* Warning! This function will fail or give invalid outputs on bad inputs! *)
Ltac2 match_of_mapped_edges_verts (domain : Graph.t) (codomain : Graph.t)
  (vs : (int * int) list) (es : (int * int) list) : Match.t :=
  (* Get all mentioned vertices *)
  let int_tag := FSet.Tags.int_tag in 
  let edge_map := List.fold_right (fun (e, e') m => FMap.add e e' m) 
    es (FMap.empty int_tag) in 
  let edge_vertex_bindings := 
    List.flat_map (fun (e, e') => 
      let ed := Graph.edge_data domain e in 
      let ed' := Graph.edge_data codomain e' in 
      let s_binds := List.combine (EData.source ed) (EData.source ed') in 
      let t_binds := List.combine (EData.target ed) (EData.target ed') in 
      List.append s_binds t_binds) es in 
  let vertex_map := List.fold_right (fun (v, v') m => FMap.add v v' m) 
    (List.append edge_vertex_bindings vs) (FMap.empty int_tag) in 
  let of_list := FSetExtra.FSet.of_list in 

  let vertex_image := of_list int_tag (List.map snd (FMap.bindings vertex_map)) in 
  let edge_image := of_list int_tag (List.map snd (FMap.bindings edge_map)) in 

  Match.make_from domain codomain vertex_map vertex_image edge_map edge_image.

(* Note that values of edges are currently unchecked in this 
  parser and purely aesthetic *)
Ltac2 Notation 
  "!Match" domain(tactic(0)) "with" codomain(tactic(0)) "mapping"
    edges(list0( (* A list of edges, each of which look like... *)
      seq(seq(tactic(0), opt(seq("(", ident, ")"))), (* Index and optional value *)
        "->", 
          seq(tactic(0), opt(seq("(", ident, ")"))))
      , ","))
    verts(opt(seq("and", 
      list1( (* A list of vertices, each of which look like... *)
      seq(seq(tactic(0), opt(seq("(", ident, ")"))), (* Index and optional value *)
        "->", 
          seq(tactic(0), opt(seq("(", ident, ")"))))
      , ",")))) : 2 :=
      (* TODO: At the very least test values are equal, and ideally test they're equal to their values in the domain / codomain*)
  let edges' := List.map (fun ((e, _),(e', _)) => (e, e')) edges in 
  let verts' := Option.map_default 
    (List.map (fun ((v, _),(v', _)) => (v, v'))) [] verts in 
  match_of_mapped_edges_verts domain codomain verts' edges'.

(* FIXME: Move *)
Ltac2 string_of_int (i : int) : string :=
  Message.to_string (Message.of_int i).

(* Create a simple graph with two vertices connected by an edge *)
Ltac2 make_simple_graph (value : string) : Graph.t :=
  let g := Graph.make () in
  let (g, v1) := Graph.add_vertex None None g in
  let (g, v2) := Graph.add_vertex None None g in
  let (g, _) := Graph.add_edge (Some value) None [v1] [v2] g in
  let g := Graph.set_outputs [v2] (Graph.set_inputs [v1] g) in 
  g.


(* Create a cycle graph of 3 vertices and 3 edges *)
Ltac2 make_cycle_graph : unit -> Graph.t := fun () =>
  let g := Graph.make () in
  let (g, v1) := Graph.add_vertex (Some "f") None g in
  let (g, v2) := Graph.add_vertex (Some "f") None g in
  let (g, v3) := Graph.add_vertex (Some "f") None g in
  let (g, _) := Graph.add_edge None None [v1] [v2] g in
  let (g, _) := Graph.add_edge None None [v2] [v3] g in
  let (g, _) := Graph.add_edge None None [v3] [v1] g in
  g.

(* Create a path graph (vertices connected in a line) *)
Ltac2 make_path_graph (values : string list) :=
  let g := Graph.make () in
  let rec add_vertices g := fun l => match l with 
    | [] => (g, [])
    | v :: rest =>
        let (g, vid) := Graph.add_vertex (Some v) None g in
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
        let (g, _) := Graph.add_edge (Some (String.app "e" (string_of_int edge_num))) None [v1] [v2] g in
        add_edges g (v2 :: rest) (Int.add edge_num 1)
    end
    end
  in
  add_edges g vertex_ids 1.

(* Create a hypergraph with scalar edges (0-ary edges) *)
Ltac2 make_scalar_graph : unit -> Graph.t := fun () =>
  let g := Graph.make () in
  let (g, _) := Graph.add_edge (Some "scalar1") None [] [] g in
  let (g, _) := Graph.add_edge (Some "scalar2") None [] [] g in
  g.

(* Create a star graph (one central vertex connected to multiple leaves) *)
Ltac2 make_star_graph (center_value : string) (leaf_values : string list) : Graph.t :=
  let g := Graph.make () in
  let (g, center) := Graph.add_vertex (Some center_value) None g in
  let rec add_leaves g leaves_remaining edge_num := match leaves_remaining with
    | [] => g
    | leaf_val :: rest =>
        let (g, leaf) := Graph.add_vertex (Some leaf_val) None g in
        let (g, _) := Graph.add_edge (Some (String.app "edge" (string_of_int edge_num))) None [center] [leaf] g in
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
  let (g, _) := Graph.add_edge (Some "f") None [v1; v2] [v3] g in
  let (g, _) := Graph.add_edge (Some "g") None [v3] [v4] g in
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
  let (g, _) := Graph.add_edge (Some "f") None [v1; v2] [v3] g in
  let (g, _) := Graph.add_edge (Some "g") None [v3] [v4] g in
  let (g, _) := Graph.add_edge (Some "g") None [v4] [v5] g in
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

End caml_test_graphs.

Module camltest_graph.

Import HypercamlInterface.


Ltac2 test_make_graph () : UTest.t :=
  let g := Graph.make () in
  UTest.seqs [
  UTest.int_eqv "empty graph has 0 Graph.vertices" 0 (Graph.num_vertices g);
  UTest.int_eqv "empty graph has 0 edges" 0 (Graph.num_edges g)].

Ltac2 test_add_vertex () : UTest.t :=
  let g := Graph.make () in
  let (g, v1) := Graph.add_vertex (Some "test") None g in
  let vdata := Graph.vertex_data g v1 in
  UTest.seqs [UTest.int_eqv "g has 1 vertex" 1 (Graph.num_vertices g);
  UTest.string_eqv "vertex has correct value" "test" (VData.value vdata)].

Ltac2 test_add_edge () : UTest.t :=
  let g := Graph.make () in
  let (g, v1) := Graph.add_vertex (Some "Graph.source") None g in
  let (g, v2) := Graph.add_vertex (Some "Graph.target") None g in
  let (g, e1) := Graph.add_edge (Some "test_edge") None [v1] [v2] g in
  UTest.seqs [
  UTest.int_eqv "g has 1 edge" 1 (Graph.num_edges g);
  let edata := Graph.edge_data g e1 in
  UTest.string_eqv "edge has correct value" "test_edge" (EData.value edata)].

Ltac2 test_inputs_outputs () : UTest.t :=
  let g := Graph.make () in
  let (g, v1) := Graph.add_vertex None None g in 
  let (g, v2) := Graph.add_vertex None None g in
  let g := Graph.set_outputs [v2] (Graph.set_inputs [v1] g) in
  UTest.seqs [
  UTest.bool_eqv "v1 is input" true (Graph.is_input g v1);
  UTest.bool_eqv "v2 is output" true (Graph.is_output g v2);
  UTest.bool_eqv "v1 is boundary" true (Graph.is_boundary g v1)].

Ltac2 test_named_vertices () : UTest.t :=
  let g := Graph.make () in
  let (g, v1) := Graph.add_vertex (Some "named_vertex") (Some 42) g in
  let vdata := Graph.vertex_data g v1 in
  UTest.seqs [
  UTest.int_eqv "vertex has correct name" 42 v1;
  UTest.string_eqv "named vertex has correct value" "named_vertex" (VData.value vdata);
  UTest.int_eqv "vindex updated correctly" 43 (Graph.vindex g)].

Ltac2 test_named_edges () : UTest.t :=
  let g := Graph.make () in
  let (g, v1) := Graph.add_vertex None None g in
  let (g, v2) := Graph.add_vertex None None g in 
  let (g, e1) := Graph.add_edge (Some "named_edge") (Some 100) [v1] [v2] g in
  let edata := Graph.edge_data g e1 in
  UTest.seqs [
  UTest.int_eqv "edge has correct name" 100 e1;
  UTest.string_eqv "named edge has correct value" "named_edge" (EData.value edata);
  UTest.int_eqv "eindex updated correctly" 101 (Graph.eindex g)].

Ltac2 test_hyperedge_multiple_vertices () : UTest.t :=
  let g := Graph.make () in
  let (g, v1) := Graph.add_vertex (Some "v1") None g in
  let (g, v2) := Graph.add_vertex (Some "v2") None g in
  let (g, v3) := Graph.add_vertex (Some "v3") None g in
  let (g, v4) := Graph.add_vertex (Some "v4") None g in
  let (g, e1) := Graph.add_edge (Some "multi_edge") None [v1; v2] [v3; v4] g in
  
  let edata := Graph.edge_data g e1 in
  
  (* Check that Graph.source Graph.vertices have the edge in their Graph.out_edges *)
  let v1_data := Graph.vertex_data g v1 in
  let v2_data := Graph.vertex_data g v2 in
  
  (* Check that Graph.target Graph.vertices have the edge in their Graph.in_edges *)
  let v3_data := Graph.vertex_data g v3 in
  let v4_data := Graph.vertex_data g v4 in

  UTest.seqs [
  UTest.int_list_eqv "edge has correct Graph.sources" [v1; v2] (EData.source edata);
  UTest.int_list_eqv "edge has correct Graph.targets" [v3; v4] (EData.target edata);
  
  (* Check that Graph.source Graph.vertices have the edge in their Graph.out_edges *)
  UTest.bool_eqv "v1 has edge in Graph.out_edges" true (FSet.mem e1 (VData.out_edges v1_data));
  UTest.bool_eqv "v2 has edge in Graph.out_edges" true (FSet.mem e1 (VData.out_edges v2_data));
  
  (* Check that Graph.target Graph.vertices have the edge in their Graph.in_edges *)
  UTest.bool_eqv "v3 has edge in Graph.in_edges" true (FSet.mem e1 (VData.in_edges v3_data));
  UTest.bool_eqv "v4 has edge in Graph.in_edges" true (FSet.mem e1 (VData.in_edges v4_data))].

Ltac2 test_vertex_edge_lists () : UTest.t :=
  let g := Graph.make () in
  let (g, v1) := Graph.add_vertex None None g in
  let (g, v2) := Graph.add_vertex None None g in
  let (g, e1) := Graph.add_edge None None [v1] [v2] g in
  
  let vertex_list := Graph.vertices g in
  let edge_list := Graph.edges g in
  
  UTest.seqs [
  UTest.int_eqv "correct number of Graph.vertices in list" 2 (List.length vertex_list);
  UTest.int_eqv "correct number of edges in list" 1 (List.length edge_list);
  UTest.bool_eqv "v1 in vertex list" true (List.mem Int.equal v1 vertex_list);
  UTest.bool_eqv "v2 in vertex list" true (List.mem Int.equal v2 vertex_list);
  UTest.bool_eqv "e1 in edge list" true (List.mem Int.equal e1 edge_list)].

Ltac2 test_source_target_functions () : UTest.t :=
  let g := Graph.make () in
  let (g, v1) := Graph.add_vertex (Some "Graph.source_v") None g in
  let (g, v2) := Graph.add_vertex (Some "Graph.target_v") None g in
  let (g, v3) := Graph.add_vertex (Some "another_source") None g in
  let (g, e1) := Graph.add_edge (Some "test_edge") None [v1; v3] [v2] g in
  
  let sources := Graph.source g e1 in
  let targets := Graph.target g e1 in
  UTest.seqs [
  UTest.int_list_eqv "correct Graph.source Graph.vertices" [v1; v3] sources;
  UTest.int_list_eqv "correct Graph.target Graph.vertices" [v2] targets].

Ltac2 test_in_out_edges () : UTest.t :=
  let g := Graph.make () in
  let (g, v1) := Graph.add_vertex None None g in
  let (g, v2) := Graph.add_vertex None None g in
  let (g, v3) := Graph.add_vertex None None g in
  let (g, e1) := Graph.add_edge None None [v1] [v2] g in
  let (g, e2) := Graph.add_edge None None [v2] [v3] g in
  let (g, e3) := Graph.add_edge None None [v1] [v3] g in
  
  (* v1 should have e1 and e3 as Graph.out_edges *)
  let v1_out := Graph.out_edges g v1 in

  (* v2 should have e1 as in_edge and e2 as out_edge *)
  let v2_in := Graph.in_edges g v2 in
  let v2_out := Graph.out_edges g v2 in

  (* v3 should have e2 and e3 as Graph.in_edges *)
  let v3_in := Graph.in_edges g v3 in

  UTest.seqs [
  (* v1 should have e1 and e3 as Graph.out_edges *)
  UTest.int_eqv "v1 has 2 Graph.out_edges" 2 (FSet.cardinal v1_out);
  UTest.bool_eqv "v1 Graph.out_edges contains e1" true (FSet.mem e1 v1_out);
  UTest.bool_eqv "v1 Graph.out_edges contains e3" true (FSet.mem e3 v1_out);
  
  (* v2 should have e1 as in_edge and e2 as out_edge *)
  UTest.int_eqv "v2 has 1 in_edge" 1 (FSet.cardinal v2_in);
  UTest.int_eqv "v2 has 1 out_edge" 1 (FSet.cardinal v2_out);
  UTest.bool_eqv "v2 Graph.in_edges contains e1" true (FSet.mem e1 v2_in);
  UTest.bool_eqv "v2 Graph.out_edges contains e2" true (FSet.mem e2 v2_out);
  
  (* v3 should have e2 and e3 as Graph.in_edges *)
  UTest.int_eqv "v3 has 2 Graph.in_edges" 2 (FSet.cardinal v3_in);
  UTest.bool_eqv "v3 Graph.in_edges contains e2" true (FSet.mem e2 v3_in);
  UTest.bool_eqv "v3 Graph.in_edges contains e3" true (FSet.mem e3 v3_in)].

Ltac2 test_complex_inputs_outputs () : UTest.t :=
  let g := Graph.make () in
  let (g, v1) := Graph.add_vertex (Some "input1") None g in
  let (g, v2) := Graph.add_vertex (Some "input2") None g in
  let (g, v3) := Graph.add_vertex (Some "output1") None g in
  let (g, v4) := Graph.add_vertex (Some "output2") None g in
  let (g, v5) := Graph.add_vertex (Some "internal") None g in
  
  let g := Graph.set_outputs [v3; v4] (Graph.set_inputs [v1; v2] g) in
  
  (* Test Graph.inputs *)
  let input_list := Graph.inputs g in
  
  (* Test outputs *)
  let output_list := Graph.outputs g in

  UTest.seqs [
  (* Test Graph.inputs *)
  UTest.int_list_eqv "correct input list" [v1; v2] input_list;
  UTest.bool_eqv "v1 is input" true (Graph.is_input g v1);
  UTest.bool_eqv "v2 is input" true (Graph.is_input g v2);
  UTest.bool_eqv "v5 is not input" false (Graph.is_input g v5);
  
  (* Test outputs *)
  UTest.int_list_eqv "correct output list" [v3; v4] output_list;
  UTest.bool_eqv "v3 is output" true (Graph.is_output g v3);
  UTest.bool_eqv "v4 is output" true (Graph.is_output g v4);
  UTest.bool_eqv "v5 is not output" false (Graph.is_output g v5);
  
  (* Test boundary *)
  UTest.bool_eqv "v1 is boundary" true (Graph.is_boundary g v1);
  UTest.bool_eqv "v2 is boundary" true (Graph.is_boundary g v2);
  UTest.bool_eqv "v3 is boundary" true (Graph.is_boundary g v3);
  UTest.bool_eqv "v4 is boundary" true (Graph.is_boundary g v4);
  UTest.bool_eqv "v5 is not boundary" false (Graph.is_boundary g v5)].

Ltac2 test_input_output_indices () : UTest.t :=
  let g := Graph.make () in
  let (g, v1) := Graph.add_vertex None None g in
  let (g, v2) := Graph.add_vertex None None g in
  let (g, v3) := Graph.add_vertex None None g in
  
  let g := Graph.set_outputs [v2; v3] (* v2 at index 0, v3 at index 1 *)
          (Graph.set_inputs [v1; v2; v1] g)  (* v1 appears at g indices 0 and 2 *)
          in
  
  let v1_data := Graph.vertex_data g v1 in
  let v2_data := Graph.vertex_data g v2 in
  let v3_data := Graph.vertex_data g v3 in
  
  UTest.seqs [
  (* Check input indices *)
  UTest.bool_eqv "v1 has input index 0" true (FSet.mem 0 (VData.in_indices v1_data));
  UTest.bool_eqv "v1 has input index 2" true (FSet.mem 2 (VData.in_indices v1_data));
  UTest.bool_eqv "v2 has input index 1" true (FSet.mem 1 (VData.in_indices v2_data));
  
  (* Check output indices *)
  UTest.bool_eqv "v2 has output index 0" true (FSet.mem 0 (VData.out_indices v2_data));
  UTest.bool_eqv "v3 has output index 1" true (FSet.mem 1 (VData.out_indices v3_data));
  UTest.bool_eqv "v1 has no output indices" true (FSet.is_empty (VData.out_indices v1_data))].



Ltac2 test_error_handling () : UTest.t :=
  let g := Graph.make () in
  let (g, v1) := Graph.add_vertex None None g in
  let (_g, _e1) := Graph.add_edge None None [v1] [v1] g in  (* self-loop *)
  
  fun _info warn _err () => 
  warn (Message.of_string "Ltac2 cannot currently test for (fatal) exceptions, so this test is skipped");
  true
  (* 
  (* Test accessing non-existent vertex *)
  Alcotest.check_raises "non-existent vertex raises exception" 
    (Graph.Graph_error "Vertex 999 not found") 
    (fun () => ignore (Graph.vertex_data g 999));
  
  (* Test accessing non-existent edge *)
  Alcotest.check_raises "non-existent edge raises exception" 
    (Graph.Graph_error "Edge 999 not found") 
    (fun () => ignore (Graph.edge_data g 999)) *).

Ltac2 test_empty_edge () : UTest.t :=
  let g := Graph.make () in
  let (g, e1) := Graph.add_edge (Some "empty_edge") None [] [] g in
  
  let edata := Graph.edge_data g e1 in
  UTest.seqs [
  UTest.int_list_eqv "empty edge has no Graph.sources" [] (EData.source edata);
  UTest.int_list_eqv "empty edge has no Graph.targets" [] (EData.target edata);
  UTest.string_eqv "empty edge has correct value" "empty_edge" (EData.value edata)].

Ltac2 test_string_of_edata () : UTest.t :=
  let edata := EData.make_from [1; 2] [3] "test_edge" in
  let str_repr := EData.string_of_edata edata in
  let expected := "Edge: test_edge ([1; 2], [3])" in
  UTest.string_eqv "string representation is correct" expected str_repr.

Ltac2 test_update_inputs_outputs () : UTest.t :=
  let g := Graph.make () in
  let (g, v1) := Graph.add_vertex None None g in
  let (g, v2) := Graph.add_vertex None None g in
  let (g, v3) := Graph.add_vertex None None g in
  
  (* Set initial Graph.inputs and outputs *)
  let g := Graph.set_outputs [v2] (Graph.set_inputs [v1] g) in
  
  (* Update Graph.inputs and outputs *)
  let g := Graph.set_outputs [v1] (Graph.set_inputs [v2; v3] g) in  
  UTest.seqs [
  (* Check that old indices are cleared *)
  UTest.bool_eqv "v1 is no longer input" false (Graph.is_input g v1);
  UTest.bool_eqv "v2 is no longer output" false (Graph.is_output g v2);
  
  (* Check new Graph.inputs and outputs *)
  UTest.bool_eqv "v2 is now input" true (Graph.is_input g v2);
  UTest.bool_eqv "v3 is now input" true (Graph.is_input g v3);
  UTest.bool_eqv "v1 is now output" true (Graph.is_output g v1)].

Ltac2 graph_tests () := [
  ("make_graph", test_make_graph);
  ("add_vertex", test_add_vertex);
  ("add_edge", test_add_edge);
  ("inputs_outputs", test_inputs_outputs);
  ("named_vertices", test_named_vertices);
  ("named_edges", test_named_edges);
  ("hyperedge_multiple_vertices", test_hyperedge_multiple_vertices);
  ("vertex_edge_lists", test_vertex_edge_lists);
  ("source_target_functions", test_source_target_functions);
  ("in_out_edges", test_in_out_edges);
  ("complex_inputs_outputs", test_complex_inputs_outputs);
  ("input_output_indices", test_input_output_indices);
  ("error_handling", test_error_handling);
  ("empty_edge", test_empty_edge);
  ("string_of_edata", test_string_of_edata);
  ("update_inputs_outputs", test_update_inputs_outputs)
].

Ltac2 Eval UTest.asserts UTest.noprint (graph_tests ()).

End camltest_graph.

Module camltest_match.

Import HypercamlInterface.
Import caml_test_graphs.

(* Empty graphs should match *)
Ltac2 test_empty_graphs () : UTest.t :=
  let g1 := Graph.make () in
  let g2 := Graph.make () in
  let matches := Match.match_graph g1 g2 in
  UTest.int_eqv "empty graphs should produce one match" 1 (Match.count matches).

(* Single vertex should match single vertex with same value *)
Ltac2 test_single_vertex_match () : UTest.t :=
  let g1 := Graph.make () in
  let (g1, _) := Graph.add_vertex (Some "test") None g1 in
  let g2 := Graph.make () in
  let (g2, _) := Graph.add_vertex (Some "test") None g2 in
  let matches := Match.match_graph g1 g2 in
  UTest.int_eqv "single vertex should match" 1 (Match.count matches).

(* Single vertex should not match if values differ *)
Ltac2 test_single_vertex_no_match () : UTest.t :=
  let g1 := Graph.make () in
  let (g1, _) := Graph.add_vertex (Some "test1") None g1 in
  let g2 := Graph.make () in
  let (g2, _) := Graph.add_vertex (Some "test2") None g2 in
  let matches := Match.match_graph g1 g2 in
  UTest.int_eqv "vertices with different values should not match" 0 (Match.count matches).

(* Simple edge should match *)
Ltac2 test_simple_edge_match () : UTest.t :=
  let g1 := make_simple_graph "edge1" in
  let g2 := make_simple_graph "edge1" in
  let matches := Match.match_graph g1 g2 in
  UTest.bool_eqv "simple edges should match" true (Int.gt (Match.count matches) 0).

(* Simple edge should not match if edge values differ *)
Ltac2 test_simple_edge_no_match () : UTest.t :=
  let g1 := make_simple_graph "edge1" in
  let g2 := make_simple_graph "edge2" in
  let matches := Match.match_graph g1 g2 in
  UTest.int_eqv "edges with different values should not match" 0 (Match.count matches).

(* Local isomorphism matching - vertices must have same degree *)
Ltac2 test_subgraph_matching () : UTest.t :=
  UTest.seqs [ (
  (* Create identical small graphs that should match *)
  let g1 := Graph.make () in
  let (g1, v1) := Graph.add_vertex (Some "A") None g1 in
  let (g1, v2) := Graph.add_vertex (Some "B") None g1 in
  let (g1, _) := Graph.add_edge (Some "e1") None [v1] [v2] g1 in
  
  let g2 := Graph.make () in
  let (g2, u1) := Graph.add_vertex (Some "A") None g2 in
  let (g2, u2) := Graph.add_vertex (Some "B") None g2 in
  let (g2, _) := Graph.add_edge (Some "e1") None [u1] [u2] g2 in
  
  let matches := Match.match_graph g1 g2 in
  UTest.bool_eqv "identical graphs should match" true (Int.gt (Match.count matches) 0));
  
  (* Test that degree constraints prevent matching into larger graphs *)
  let large_path := make_path_graph ["A"; "B"; "C"] in
  let small_path := make_path_graph ["A"; "B"] in
  let no_matches := Match.match_graph small_path large_path in
  UTest.int_eqv "degree constraints prevent subgraph matching" 0 (Match.count no_matches)].


(* Cycle should match itself 3 times *)
Ltac2 test_cycle_self_match () : UTest.t :=
  let cycle := make_cycle_graph () in
  let matches := Match.match_graph cycle cycle in
  UTest.int_eqv "cycle should match itself three times" 3 (Match.count matches).

(* cycle should not match path *)
Ltac2 test_cycle_path_no_match () : UTest.t :=
  let cycle := make_cycle_graph () in
  let path := make_path_graph ["A"; "B"; "C"] in
  let matches := Match.match_graph cycle path in
  UTest.int_eqv "cycle should not match path (different topology)" 0 (Match.count matches).

(* Scalar edges should match *)
Ltac2 test_scalar_match () : UTest.t :=
  let g1 := make_scalar_graph () in
  let g2 := make_scalar_graph () in
  let matches := Match.match_graph g1 g2 in
  UTest.bool_eqv "scalar graphs should match" true (Int.gt (Match.count matches) 0).

(* Star graphs should match with same structure *)
Ltac2 test_star_match () : UTest.t :=
  let star1 := make_star_graph "center" ["leaf1"; "leaf2"] in
  let star2 := make_star_graph "center" ["leaf1"; "leaf2"] in
  let matches := Match.match_graph star1 star2 in
  UTest.bool_eqv "star graphs should match" true (Int.gt (Match.count matches) 0).

(* Star graphs with different number of leaves - degree constraints *)
Ltac2 test_star_different_size () : UTest.t :=
  let star1 := make_star_graph "center" ["leaf1"; "leaf2"] in
  let star2 := make_star_graph "center" ["leaf1"; "leaf2"] in
  let star3 := make_star_graph "center" ["leaf1"; "leaf2"; "leaf3"] in
  let matches := Match.match_graph star1 star2 in

  UTest.seqs [ (
  (* Two identical star graphs should match *)
  UTest.bool_eqv "identical star graphs should match" true (Int.gt (Match.count matches) 0) ); (
  
  (* Different sized stars should not match due to degree constraints *)
  let no_matches := Match.match_graph star1 star3 in
  UTest.int_eqv "different sized stars should not match" 0 (Match.count no_matches) ); (
  let reverse_no_matches := Match.match_graph star3 star1 in
  UTest.int_eqv "reverse should also not match" 0 (Match.count reverse_no_matches) ); (
  
  (* Test with different leaf names - should not match *)
  let star4 := make_star_graph "center" ["different1"; "different2"] in
  let name_no_matches := Match.match_graph star1 star4 in
  UTest.int_eqv "stars with different leaf names should not match" 0 (Match.count name_no_matches))].

(* Boundary graphs should respect boundary constraints *)
Ltac2 test_boundary_matching () : UTest.t :=
  let g1 := make_boundary_graph () in
  let g2 := make_boundary_graph () in
  let matches := Match.match_graph g1 g2 in
  UTest.bool_eqv "boundary graphs should match" true (Int.gt (Match.count matches) 0).

(* FIXME: Move *)
Ltac2 is_some : 'a option -> bool := fun o =>
  Option.map_default (fun _ => true) false o.
(* FIXME: Move *)
Ltac2 is_none : 'a option -> bool := fun o =>
  Option.map_default (fun _ => false) true o.

(* Test isomorphism finding *)
Ltac2 test_find_iso () : UTest.t :=
  let g1 := make_cycle_graph () in
  let g2 := make_cycle_graph () in
  let iso_opt := Match.find_iso g1 g2 in
  UTest.bool_eqv "cycles should be isomorphic" true (is_some iso_opt).

(* Non-isomorphic graphs *)
Ltac2 test_no_iso () : UTest.t :=
  let cycle := make_cycle_graph () in
  let path := make_path_graph ["A"; "B"; "C"] in
  let iso_opt := Match.find_iso cycle path in
  UTest.bool_eqv "cycle and path should not be isomorphic" true (is_none iso_opt).

(* Complex hypergraph matching *)
Ltac2 test_hypergraph_match () : UTest.t :=
  let g1 := Graph.make () in
  let (g1, v1) := Graph.add_vertex (Some "A") None g1 in
  let (g1, v2) := Graph.add_vertex (Some "B") None g1 in
  let (g1, v3) := Graph.add_vertex (Some "C") None g1 in
  let (g1, _) := Graph.add_edge (Some "hyper") None [v1; v2] [v3] g1 in
  
  let g2 := Graph.make () in
  let (g2, u1) := Graph.add_vertex (Some "A") None g2 in
  let (g2, u2) := Graph.add_vertex (Some "B") None g2 in
  let (g2, u3) := Graph.add_vertex (Some "C") None g2 in
  let (g2, _) := Graph.add_edge (Some "hyper") None [u1; u2] [u3] g2 in
  
  let matches := Match.match_graph g1 g2 in
  UTest.bool_eqv "hypergraphs should match" true (Int.gt (Match.count matches) 0).

(* Test multiple matches (symmetries) *)
Ltac2 test_multiple_matches () : UTest.t :=
  let g1 := Graph.make () in
  let (g1, _) := Graph.add_vertex (Some "same") None g1 in
  let (g1, _) := Graph.add_vertex (Some "same") None g1 in
  
  let g2 := Graph.make () in
  let (g2, _) := Graph.add_vertex (Some "same") None g2 in
  let (g2, _) := Graph.add_vertex (Some "same") None g2 in
  
  let matches := Match.match_graph g1 g2 in
  UTest.bool_eqv "should find multiple matches due to symmetry" true (Int.ge (Match.count matches) 2).

(* Mixed edge types *)
Ltac2 test_mixed_edges () : UTest.t :=
  let g1 := Graph.make () in
  let (g1, v1) := Graph.add_vertex (Some "A") None g1 in
  let (g1, v2) := Graph.add_vertex (Some "B") None g1 in
  let (g1, _) := Graph.add_edge (Some "normal") None [v1] [v2] g1 in
  let (g1, _) := Graph.add_edge (Some "scalar") None [] [] g1 in
  
  let g2 := Graph.make () in
  let (g2, u1) := Graph.add_vertex (Some "A") None g2 in
  let (g2, u2) := Graph.add_vertex (Some "B") None g2 in
  let (g2, _) := Graph.add_edge (Some "normal") None [u1] [u2] g2 in
  let (g2, _) := Graph.add_edge (Some "scalar") None [] [] g2 in
  
  let matches := Match.match_graph g1 g2 in
  UTest.bool_eqv "graphs with mixed edge types should match" true (Int.gt (Match.count matches) 0).

(* Match proper hypergraph on another *)
Ltac2 test_hypergraph_match_proper () : UTest.t :=
  let g1 := make_hgraph () in
  let g2 := make_hgraph2 () in
  let matches := Match.match_graph g1 g2 in
  UTest.seq (fun info _warn _err () => 
    List.iter (fun m => info (Match.print m)) (Match.seq_to_list matches);
    true)
  (UTest.int_eqv "proper hypergraphs should match" 1 (Match.count matches)).

Ltac2 tests () := [
  ("empty graphs match", test_empty_graphs);
  ("single vertex match", test_single_vertex_match);
  ("single vertex no match", test_single_vertex_no_match);
  ("simple edge match", test_simple_edge_match);
  ("simple edge no match", test_simple_edge_no_match);
  ("subgraph matching", test_subgraph_matching);
  ("cycle self match", test_cycle_self_match);
  ("cycle path no match", test_cycle_path_no_match);
  ("scalar match", test_scalar_match);
  ("star match", test_star_match);
  ("star different size", test_star_different_size);
  ("boundary matching", test_boundary_matching);
  ("find isomorphism", test_find_iso);
  ("no isomorphism", test_no_iso);
  ("hypergraph match", test_hypergraph_match);
  ("multiple matches", test_multiple_matches);
  ("mixed edges", test_mixed_edges);
  ("hypergraph match proper", test_hypergraph_match_proper)
].

Ltac2 Eval UTest.asserts UTest.noprint (tests()).

End camltest_match.

Module camlgraph.

Import HypercamlInterface.

Ltac2 graph_g : unit -> Graph.t := fun () =>
  let g := Graph.make () in
  let (g, v1) := Graph.add_vertex None None g in
  let (g, v2) := Graph.add_vertex None None g in
  let (g, v3) := Graph.add_vertex None None g in
  let (g, v4) := Graph.add_vertex None None g in
  let (g, _) := Graph.add_edge (Some "f") None [v1; v2] [v3] g in
  let (g, _) := Graph.add_edge (Some "g") None [v3] [v4] g in
  let g := Graph.set_outputs [v4] (Graph.set_inputs [v1; v2] g) in 
  g.

Ltac2 graph_h : unit -> Graph.t := fun () =>
  let h := Graph.make () in
  let (h, v1) := Graph.add_vertex None None h in
  let (h, v2) := Graph.add_vertex None None h in
  let (h, v3) := Graph.add_vertex None None h in
  let (h, v4) := Graph.add_vertex None None h in
  let (h, v5) := Graph.add_vertex None None h in
  let (h, _) := Graph.add_edge (Some "f") None [v1; v2] [v3] h in
  let (h, _) := Graph.add_edge (Some "g") None [v3] [v4] h in
  let (h, _) := Graph.add_edge (Some "g") None [v4] [v5] h in
  let h := Graph.set_outputs [v5] (Graph.set_inputs [v1; v2] h) in 
  h.


Import caml_test_graphs.

Ltac2 graph_g_alt () : Graph.t := !Graph 0, 1 -> 3 : 
  f : 0, 1 -> 2 ; g : 2 -> 3.
Ltac2 graph_h_alt () : Graph.t := !Graph 0, 1 -> 4 : 
  f (0) : 0, 1 -> 2; g (1) : 2 -> 3; g (2) : 3 -> 4.

Ltac2 graph_g_diff () : Graph.t := !Graph 0, 1 -> 4 : 
  f : 0, 1 -> 2 ; g : 3 -> 4.
Ltac2 graph_h_diff () : Graph.t := !Graph 0, 1 -> 4,6 : 
  f (0) : 0, 1 -> 2; g (1) : 3 -> 4; g (2) : 5 -> 6.

Ltac2 Eval Graph.equal (graph_h()) (graph_h_alt()).
Ltac2 Eval Graph.equal (graph_h()) (graph_h_diff()).


Ltac2 Eval Match.count (Match.match_graph (graph_g ()) (graph_h ())).
Ltac2 Eval Match.count (Match.match_graph (graph_g_diff ()) (graph_g_diff ())).

Ltac2 Eval List.map Match.print_nice_full
  (Match.seq_to_list (Match.match_graph (graph_g_diff ()) (graph_h_diff ()))).


Ltac2 match_ex () : Match.t := 
  !Match (graph_g_diff()) with (graph_h_diff()) mapping 
    0 (f) -> 0 (f), 1 (g) -> 2 (g).

Ltac2 Eval Message.print (Match.print_nice_full (match_ex())).
Ltac2 Eval Match.equal (match_ex()) (!Match (!Graph 0, 1 -> 4 : f (0) : 0, 1 -> 2; g (1) : 3 -> 4 ) with
  (!Graph 0, 1 -> 4, 6 : f (0) : 0, 1 -> 2; g (1) : 3 -> 4; g (2) : 5 -> 6 )
  mapping 0 (f) -> 0 (f), 1 (g) -> 2 (g)).

Ltac2 Eval Message.print (Graph.print_nice (graph_g ())).
Ltac2 Eval Message.print (Graph.print_nice (!Graph 0, 1 -> 3 : 
  f : 0 , 1 -> 2 ; g (3) : 2 -> 3)).
Ltac2 Eval Message.print (Graph.print_nice (graph_h ())).

(* Ltac2 readme_test () : UTest.t :=
  UTest.int_eqv  *)

Ltac2 Eval Match.count (Match.match_graph (graph_g ()) (graph_h ())).
Ltac2 Eval 
  let ms := Match.seq_to_list (Match.match_graph (graph_g ()) (graph_h ())) in 
  List.iter (fun m => Message.print (Match.print m)) ms.

End camlgraph.
