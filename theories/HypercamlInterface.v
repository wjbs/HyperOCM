From Ltac2 Require Import Ltac2.

Declare ML Module "hypercaml_interface:hyperocm.hypercaml_interface".

Module VData.

Ltac2 Type t.

Ltac2 @external equal : t -> t -> bool 
  := "hyperocm.hypercaml_interface" "vdata_equal".

Ltac2 @external make : string -> t
  := "hyperocm.hypercaml_interface" "vdata_make".

Ltac2 @external make_from : int FSet.t -> int FSet.t -> 
  int FSet.t -> int FSet.t -> string -> t
  := "hyperocm.hypercaml_interface" "vdata_make_from".

Ltac2 @external in_edges : t -> int FSet.t
  := "hyperocm.hypercaml_interface" "vdata_in_edges".

Ltac2 @external out_edges : t -> int FSet.t
  := "hyperocm.hypercaml_interface" "vdata_out_edges".

Ltac2 @external in_indices : t -> int FSet.t
  := "hyperocm.hypercaml_interface" "vdata_in_indices".

Ltac2 @external out_indices : t -> int FSet.t
  := "hyperocm.hypercaml_interface" "vdata_out_indices".

Ltac2 @external value : t -> string
  := "hyperocm.hypercaml_interface" "vdata_value".

Ltac2 @external print : t -> message
  := "hyperocm.hypercaml_interface" "print_vdata".

End VData.

Module EData.

Ltac2 Type t.

Ltac2 @external equal : t -> t -> bool 
  := "hyperocm.hypercaml_interface" "edata_equal".

Ltac2 @external make : string -> t
  := "hyperocm.hypercaml_interface" "edata_make".

Ltac2 @external make_from : int list -> int list -> string -> t
  := "hyperocm.hypercaml_interface" "edata_make_from".

Ltac2 @external source : t -> int list
  := "hyperocm.hypercaml_interface" "edata_source".

Ltac2 @external target : t -> int list
  := "hyperocm.hypercaml_interface" "edata_target".

Ltac2 @external value : t -> string
  := "hyperocm.hypercaml_interface" "edata_value".

Ltac2 @external print : t -> message
  := "hyperocm.hypercaml_interface" "print_edata".

Ltac2 @external print_nice : t -> message
  := "hyperocm.hypercaml_interface" "print_edata_nice".
  
Ltac2 @external print_to_parse : t -> message
  := "hyperocm.hypercaml_interface" "print_edge_to_parse".

Ltac2 @external string_of_edata : t -> string
  := "hyperocm.hypercaml_interface" "graph_string_of_edata".

End EData.

Module Graph.

Ltac2 Type t.

Ltac2 @external print : t -> message
  := "hyperocm.hypercaml_interface" "print_graph".

Ltac2 @external print_full : t -> message
  := "hyperocm.hypercaml_interface" "print_graph_full".

Ltac2 @external print_nice : t -> message
  := "hyperocm.hypercaml_interface" "print_graph_nice".

Ltac2 @external make : unit -> t
  := "hyperocm.hypercaml_interface" "graph_make".


Ltac2 @external make_from : (int, VData.t) FMap.t -> (int, EData.t) FMap.t
  -> int list -> int list -> int -> int -> t
  := "hyperocm.hypercaml_interface" "graph_make_from".

Ltac2 @external equal : t -> t -> bool
  := "hyperocm.hypercaml_interface" "graph_equal".

Ltac2 @external vdata : t -> (int, VData.t) FMap.t
  := "hyperocm.hypercaml_interface" "graph_vdata".
Ltac2 @external edata : t -> (int, EData.t) FMap.t
  := "hyperocm.hypercaml_interface" "graph_edata".
Ltac2 @external inputs : t -> int list 
  := "hyperocm.hypercaml_interface" "graph_inputs".
Ltac2 @external outputs : t -> int list
  := "hyperocm.hypercaml_interface" "graph_outputs".
Ltac2 @external vindex : t -> int
  := "hyperocm.hypercaml_interface" "graph_vindex".
Ltac2 @external eindex : t -> int
  := "hyperocm.hypercaml_interface" "graph_eindex".


Ltac2 @external vertices : t -> int list
  := "hyperocm.hypercaml_interface" "graph_vertices".
Ltac2 @external edges : t -> int list
  := "hyperocm.hypercaml_interface" "graph_edges".

Ltac2 @external num_vertices : t -> int
  := "hyperocm.hypercaml_interface" "graph_num_vertices".
Ltac2 @external num_edges : t -> int
  := "hyperocm.hypercaml_interface" "graph_num_edges".
  
Ltac2 @external vertex_data : t -> int -> VData.t
  := "hyperocm.hypercaml_interface" "graph_vertex_data".
Ltac2 @external edge_data : t -> int -> EData.t
  := "hyperocm.hypercaml_interface" "graph_edge_data".
  
Ltac2 @external in_edges : t -> int -> int FSet.t
  := "hyperocm.hypercaml_interface" "graph_in_edges".
Ltac2 @external out_edges : t -> int -> int FSet.t
  := "hyperocm.hypercaml_interface" "graph_out_edges".

Ltac2 @external source : t -> int -> int list
  := "hyperocm.hypercaml_interface" "graph_source".
Ltac2 @external target : t -> int -> int list
  := "hyperocm.hypercaml_interface" "graph_target".


Ltac2 @external add_vertex : string option -> int option -> t -> t * int
  := "hyperocm.hypercaml_interface" "graph_add_vertex".

Ltac2 @external add_edge : string option -> int option -> 
  int list -> int list -> t -> t * int
  := "hyperocm.hypercaml_interface" "graph_add_edge".


Ltac2 @external set_inputs : int list -> t -> t
  := "hyperocm.hypercaml_interface" "graph_set_inputs".
Ltac2 @external set_outputs : int list -> t -> t
  := "hyperocm.hypercaml_interface" "graph_set_outputs".


Ltac2 @external is_input : t -> int -> bool
  := "hyperocm.hypercaml_interface" "graph_is_input".
Ltac2 @external is_output : t -> int -> bool
  := "hyperocm.hypercaml_interface" "graph_is_output".
Ltac2 @external is_boundary : t -> int -> bool
  := "hyperocm.hypercaml_interface" "graph_is_boundary".

End Graph.

Module Match.

(* TODO: Make these work with the tactic monad *)
Ltac2 @external get_debug_match : unit -> bool
  := "hyperocm.hypercaml_interface" "match_get_debug_match".
Ltac2 @external set_debug_match : bool -> unit
  := "hyperocm.hypercaml_interface" "match_set_debug_match".

Ltac2 Type t.

Ltac2 @external print : t -> message
  := "hyperocm.hypercaml_interface" "print_match".

Ltac2 @external print_nice : t -> message
  := "hyperocm.hypercaml_interface" "print_match_nice".

Ltac2 @external print_nice_full : t -> message
  := "hyperocm.hypercaml_interface" "print_match_nice_full".

Ltac2 @external make : Graph.t -> Graph.t -> t
  := "hyperocm.hypercaml_interface" "match_make".

Ltac2 @external make_from : Graph.t -> Graph.t -> (int, int) FMap.t -> 
  int FSet.t -> (int, int) FMap.t -> int FSet.t -> t
  := "hyperocm.hypercaml_interface" "match_make_from".

Ltac2 @external equal : t -> t -> bool
  := "hyperocm.hypercaml_interface" "match_equal".

Ltac2 @external domain : t -> Graph.t
  := "hyperocm.hypercaml_interface" "match_domain".
Ltac2 @external codomain : t -> Graph.t
  := "hyperocm.hypercaml_interface" "match_codomain".
Ltac2 @external vertex_map : t -> (int, int) FMap.t
  := "hyperocm.hypercaml_interface" "match_vertex_map".
Ltac2 @external vertex_image : t -> int FSet.t
  := "hyperocm.hypercaml_interface" "match_vertex_image".
Ltac2 @external edge_map : t -> (int, int) FMap.t
  := "hyperocm.hypercaml_interface" "match_edge_map".
Ltac2 @external edge_image : t -> int FSet.t
  := "hyperocm.hypercaml_interface" "match_edge_image".

Ltac2 @external try_add_vertex : int -> int -> t -> t option
  := "hyperocm.hypercaml_interface" "match_try_add_vertex".

Ltac2 @external try_add_edge : int -> int -> t -> t option
  := "hyperocm.hypercaml_interface" "match_try_add_edge".

Ltac2 @external domain_neighbourhood_mapped : t -> int -> bool
  := "hyperocm.hypercaml_interface" "match_domain_neighbourhood_mapped".

Ltac2 @external map_scalars : t -> t option
  := "hyperocm.hypercaml_interface" "match_map_scalars".

Ltac2 @external more : t -> t list
  := "hyperocm.hypercaml_interface" "match_more".


Ltac2 @external is_total : t -> bool
  := "hyperocm.hypercaml_interface" "match_is_total".
Ltac2 @external is_surjective : t -> bool
  := "hyperocm.hypercaml_interface" "match_is_surjective".
Ltac2 @external is_injective : t -> bool
  := "hyperocm.hypercaml_interface" "match_is_injective".


Ltac2 @external make_match_sequence : Graph.t -> Graph.t -> t option -> t list
  := "hyperocm.hypercaml_interface" "match_make_match_sequence".

Ltac2 @external next_match : t list -> (t * (t list)) option
  := "hyperocm.hypercaml_interface" "match_next_match".

Ltac2 @external seq_to_list : t list -> t list
  := "hyperocm.hypercaml_interface" "match_seq_to_list".

Ltac2 @external match_graph : Graph.t -> Graph.t -> t list
  := "hyperocm.hypercaml_interface" "match_match_graph".

Ltac2 @external count : t list -> int
  := "hyperocm.hypercaml_interface" "match_count".

Ltac2 @external find_iso : Graph.t -> Graph.t -> t option
  := "hyperocm.hypercaml_interface" "match_find_iso".

End Match.


(* Ltac2 Eval Message.print (VData.print (VData.make "")). *)

(* Ltac2 Eval FSet.cardinal (in_edges (make_from 
  (FSet.add 1 (in_edges (make "hi"))) [] [] [] "hello")).

Ltac2 Eval FSet.cardinal (in_edges_set (make "test")). *)

Module GraphNotation.


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
  let of_list l := List.fold_right FSet.add l (FSet.empty int_tag) in

  let vertex_image := of_list (List.map snd (FMap.bindings vertex_map)) in 
  let edge_image := of_list (List.map snd (FMap.bindings edge_map)) in 

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

End GraphNotation.