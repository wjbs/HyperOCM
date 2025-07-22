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

End EData.

Module Graph.

Ltac2 Type t.

Ltac2 @external print : t -> message
  := "hyperocm.hypercaml_interface" "print_graph".

Ltac2 @external make : unit -> t
  := "hyperocm.hypercaml_interface" "graph_make".


Ltac2 @external make_from : (int, int) FMap.t -> (int, int) FMap.t
  -> int list -> int list -> int -> int -> t
  := "hyperocm.hypercaml_interface" "graph_make_from".


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

Ltac2 @external make : Graph.t -> Graph.t -> t
  := "hyperocm.hypercaml_interface" "match_make".

Ltac2 @external make_from : Graph.t -> Graph.t -> 
  (int, int) FMap.t -> int FSet.t -> (int, int) FMap.t -> int FSet.t -> t
  := "hyperocm.hypercaml_interface" "match_make_from".


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

Ltac2 @external match_graph : Graph.t -> Graph.t -> t
  := "hyperocm.hypercaml_interface" "match_match_graph".

Ltac2 @external find_iso : Graph.t -> Graph.t -> t option
  := "hyperocm.hypercaml_interface" "match_find_iso".

End Match.


(* Ltac2 Eval Message.print (VData.print (VData.make "")). *)

(* Ltac2 Eval FSet.cardinal (in_edges (make_from 
  (FSet.add 1 (in_edges (make "hi"))) [] [] [] "hello")).

Ltac2 Eval FSet.cardinal (in_edges_set (make "test")). *)
