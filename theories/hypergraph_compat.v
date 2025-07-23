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