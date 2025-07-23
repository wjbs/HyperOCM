Require Import HyperOCM.hypergraph.

Require HypercamlInterface.

From Ltac2 Require Import Init.


Module CamlOfLtac.

Ltac2 value (v : string option) : string :=
  Option.default "" v.

Ltac2 vdata (v : string VData) : HypercamlInterface.VData.t := 
  HypercamlInterface.VData.make_from (vin_edges v) (vout_edges v) 
    (vin_indices v) (vout_indices v) (value (vvalue v)).

Ltac2 edata (e : string EData) : HypercamlInterface.EData.t := 
  HypercamlInterface.EData.make_from 
    (esource e) (etarget e) (value (evalue e)).

Ltac2 graph (g : (string, string) Graph) : HypercamlInterface.Graph.t :=
  HypercamlInterface.Graph.make_from (FMap.mapi (fun _ => vdata) (g.(vdata)))
    (FMap.mapi (fun _ => edata) (g.(edata)))
    (inputs g) (outputs g) (g.(_vindex)) (g.(_eindex)).

Ltac2 match_ (m : (string, string) Match) : HypercamlInterface.Match.t :=
  HypercamlInterface.Match.make_from 
    (graph (m.(domain))) (graph (m.(codomain))) 
    (m.(vertex_map)) (m.(vertex_image))
    (m.(edge_map)) (m.(edge_image)).

End CamlOfLtac.

Module LtacOfCaml.

Import HypercamlInterface.

Ltac2 value (v : string) : string option :=
  if String.is_empty v then None else Some v.

Ltac2 vdata (vd : VData.t) : string hypergraph.VData := 
  mk_vdata_from 
    (VData.in_edges vd) (VData.out_edges vd)
    (VData.in_indices vd) (VData.out_indices vd)
    (value (VData.value vd)).

Ltac2 edata (ed : EData.t) : string hypergraph.EData :=
  mk_edata (EData.source ed) (EData.target ed) (value (EData.value ed)).

Ltac2 graph (g : Graph.t) : (string, string) hypergraph.Graph := {
  vdata := FMap.mapi (fun _ => vdata) (Graph.vdata g);
  edata := FMap.mapi (fun _ => edata) (Graph.edata g);
  _inputs := Graph.inputs g;
  _outputs := Graph.outputs g;
  _vindex := Graph.vindex g;
  _eindex := Graph.eindex g;
}.

Ltac2 match_ (m : Match.t) : (string, string) hypergraph.Match := {
  domain := graph (Match.domain m);
  codomain := graph (Match.codomain m);
  edge_eq := String.equal;
  vertex_map := (Match.vertex_map m);
  vertex_image := (Match.vertex_image m);
  edge_map := (Match.edge_map m);
  edge_image := (Match.edge_image m);
}.

End LtacOfCaml.

Module HypermutInterface. 

Import hypergraph.

Module VData.

Ltac2 Type t := string VData.

Ltac2 equal (v : t) : t -> bool :=
  vdata_equal String.equal v.

Ltac2 make (value : string) : t :=
  mk_vdata (Some value).

Ltac2 make_from ie oe ii oi (value : string) : t :=
  mk_vdata_from ie oe ii oi (Some value).

Ltac2 in_edges (v : t) := v.(in_edges).

Ltac2 out_edges (v : t) := v.(out_edges).

Ltac2 in_indices (v : t) := v.(in_indices).

Ltac2 out_indices (v : t) := v.(out_indices).

Ltac2 value (v : t) := Option.default "" (v.(vvalue)).

Ltac2 print (v : t) : message := 
  GraphPrinting.pr_vdata Message.of_string v.

End VData.

Module EData.

Ltac2 Type t := string EData.

Ltac2 equal (e : t) : t -> bool :=
  edata_equal String.equal e.

Ltac2 make_from s t v : t := {
  s := s;
  t := t;
  value := Some v
}.

Ltac2 source (e : t) := e.(s).

Ltac2 target (e : t) := e.(t).

Ltac2 value (e : t) := Option.default "" (e.(value)).

Ltac2 print (e : t) : message := 
  GraphPrinting.pr_edata Message.of_string e.

Ltac2 string_of_edata (e : t) : string :=
  let pr_list l := Message.to_string 
    (PrintingExtra.Pp.prlist_with_sep (fun () => Message.of_string "; ")
      Message.of_int l) in 
  List.fold_right String.app ["Edge: ";
    value e; " ([";
    pr_list (source e); "], [";
    pr_list (target e); "])"] "".

End EData.

Module Graph.

Ltac2 Type t := (string, string) Graph.

Ltac2 print g := 
  GraphPrinting.print_graph Message.of_string Message.of_string g.

Ltac2 make () : t := mk_graph ().

Ltac2 make_from vd ed ins outs vi ei : t :=
  mk_graph_from vd ed ins outs vi ei.

Ltac2 equal g : t -> bool :=
  graph_equal String.equal String.equal g.

Ltac2 vdata g := g.(vdata).
Ltac2 edata g := g.(edata).
Ltac2 inputs g := inputs g.
Ltac2 outputs g := outputs g.
Ltac2 vindex g := g.(_vindex).
Ltac2 eindex g := g.(_eindex).

Ltac2 vertices g := vertices g.
Ltac2 edges g := edges g.

Ltac2 num_vertices g := num_vertices g.
Ltac2 num_edges g := num_edges g.

Ltac2 vertex_data (g : t) v := vertex_data g v.
Ltac2 edge_data (g : t) v := edge_data g v.

Ltac2 in_edges (g : t) v := in_edges g v.
Ltac2 out_edges (g : t) v := out_edges g v.

Ltac2 source (g : t) v := source g v.
Ltac2 target (g : t) v := target g v.

Ltac2 add_vertex name idx (g : t) : t * int := 
  g, add_vertex g name idx.
Ltac2 add_edge name idx s t (g : t) : t * int :=
  g, add_edge g s t name idx.

Ltac2 set_inputs ins (g : t) : t := set_inputs g ins; g.
Ltac2 set_outputs outs (g : t) : t := set_outputs g outs; g.

Ltac2 is_input (g : t) v := is_input g v.
Ltac2 is_output (g : t) v := is_output g v.
Ltac2 is_boundary (g : t) v := is_boundary g v.

End Graph.

Module Match.

Ltac2 Type t := (string, string) Match.

Ltac2 print (m : t) := Printing.print_match m.

Ltac2 make (d : Graph.t) (cd : Graph.t) : t := mk_match d cd String.equal.

Ltac2 make_from (d : Graph.t) (cd : Graph.t) vmap vimg emap eimg :=
  mk_match_from d cd String.equal vmap vimg emap eimg.

Ltac2 equal (m : t) : t -> bool :=
  match_equal String.equal String.equal m.

Ltac2 domain (m : t) : Graph.t := m.(domain).
Ltac2 codomain (m : t) : Graph.t := m.(codomain).
Ltac2 vertex_map (m : t) := m.(vertex_map).
Ltac2 vertex_image (m : t) := m.(vertex_image).
Ltac2 edge_map (m : t) := m.(edge_map).
Ltac2 edge_image (m : t) := m.(edge_image).

Ltac2 try_add_vertex dv cdv (m : t) : t option :=
  if try_add_vertex String.equal m dv cdv then Some m else None.

Ltac2 try_add_edge de cde (m : t) : t option :=
  if try_add_edge String.equal m de cde then Some m else None.

Ltac2 domain_neighbourhood_mapped (m : t) v :=
  domain_neighborhood_mapped m v.

Ltac2 map_scalars (m : t) : t option := 
  if map_scalars m then Some m else None.

Ltac2 more (m : t) : t list :=
  more String.equal m.

Ltac2 is_total (m : t) : bool := is_total m.
Ltac2 is_surjective (m : t) : bool := is_surjective m.
Ltac2 is_injective (m : t) : bool := is_injective m.

Ltac2 make_match_sequence (d : Graph.t) cd (m : t option) : t list :=
  (mk_matches String.equal d cd m false).(match_stack).

Ltac2 next_match (ms : t list) : (t * (t list)) option :=
  Option.map (fun (m, ms) => (m, ms.(match_stack)))
    (Option.bind (mk_matches_from_stack ms) (
      fun ms => Option.map (fun m => (m, ms)) 
      (next_match String.equal ms))).

Ltac2 seq_to_list (ms : t list) : t list := 
  Option.map_default (get_matches String.equal) [] (mk_matches_from_stack ms).

Ltac2 match_graph (d : Graph.t) (cd : Graph.t) : t list :=
  match_graph String.equal String.equal d cd.

Ltac2 count (ms : t list) : int :=
  Option.map_default (fun ms => List.length (get_matches String.equal ms)) 0 
    (mk_matches_from_stack ms).

Ltac2 find_iso (d : Graph.t) (cd : Graph.t) : t option :=
  find_iso String.equal String.equal d cd.

End Match.


End HypermutInterface.