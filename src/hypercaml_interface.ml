open Names
(* kernel names, ie ModPath, KerName, Id etc *)

open Ltac2_plugin
(* the Ltac2 plugin is "packaged" ie its modules are all contained in module Ltac2_plugin
   without this open we would have to refer to eg Ltac2_plugin.Tac2externals below *)

open Tac2externals
(* APIs to register new externals, including the convenience "@->" infix operator *)

open Tac2ffi
(* Translation operators between Ltac2 values and OCaml values in various types *)

open Tac2core

(* open Tac2val *)

module Graph = Graph
module NSet = Graph.NSet
module NMap = Graph.NMap

module Match = Match



(* TODO: tac2core.ml doesn't let us reuse its implementation details 
   well enough to take sets, only give them, until rocq 9.1. Talk over! *)

(* FIXME!!! This horrible hacky solution can be replaced by the comment 
   in rocq v9.1*)
let set_of_valexpr (_tag : ('a, 'set, 'map) map_tag) v : 'set =
   let (TaggedSet (_tag', s)) = v in
   (* let Refl = assert_map_tag_eq tag tag' in s *)
   Obj.magic s

let map_of_valexpr (_tag : ('a, 'set, 'map) map_tag) v : 'map =
   let (TaggedMap (_tag', s)) = v in
   (* let Refl = assert_map_tag_eq tag tag' in s *)
   Obj.magic s

let tag_int_set s = TaggedSet (int_map_tag, s)
let untag_int_set (ts : tagged_set) : Int.Set.t = 
   set_of_valexpr int_map_tag ts
let tag_int_map r m = TaggedMap (int_map_tag, NMap.map (Tac2ffi.repr_of r) m)
let untag_int_map r (ts : tagged_map) = 
   NMap.map (Tac2ffi.repr_to r) (map_of_valexpr int_map_tag ts)

(* TO DO: is this really the best way to do this? *)
(* let int_set_repr = {
   r_of = fun s -> Tac2ffi.repr_of set_repr (tag_int_set s);
   r_to = fun v -> untag_int_set (Tac2ffi.repr_to set_repr v);
} *)

(* Used to distinguish our primitives from some other plugin's primitives.
   By convention matches the plugin's ocamlfind name. *)
let plugin_name = "hyperocm.hypercaml_interface"


let pname s = { Tac2expr.mltac_plugin = plugin_name; mltac_tactic = s }

(* We define for convenience a wrapper around Tac2externals.define.
   [define "foo"] has type
   [('a, 'b) Ltac2_plugin.Tac2externals.spec -> 'b -> unit].
   Type [('a, 'b) spec] represents a high-level Ltac2 tactic specification. It
   indicates how to turn a value of type ['b] into an Ltac2 tactic.
   The type parameter ['a] gives the type of value produced by interpreting the
   specification. *)
let define s = define (pname s)

let val_vdata = Tac2dyn.Val.create (plugin_name^":vdata")
let vdata = repr_ext val_vdata

let () = define "vdata_make" (string @-> ret vdata) @@ fun value -> 
   Graph.make_vdata ~value:value ()

let () = define "vdata_make_from" 
   (set_repr @-> set_repr @-> set_repr @-> set_repr @-> string @-> ret vdata) @@
   fun in_edges out_edges in_indices out_indices value -> {
  in_edges = untag_int_set in_edges;
  out_edges = untag_int_set out_edges;
  in_indices = untag_int_set in_indices;
  out_indices = untag_int_set out_indices;
  value = value;
}

let vdata_equal (vd : Graph.vdata) (vd' : Graph.vdata) : bool = 
   NSet.equal vd.in_edges vd'.in_edges &&
   NSet.equal vd.out_edges vd'.out_edges &&
   NSet.equal vd.in_indices vd'.in_indices &&
   NSet.equal vd.out_indices vd'.out_indices &&
   String.equal vd.value vd'.value

let () = define "vdata_equal" (vdata @-> vdata @-> ret bool) @@ vdata_equal

let () = define "vdata_in_edges" (vdata @-> ret set_repr) @@ fun v -> 
   tag_int_set v.in_edges

let () = define "vdata_out_edges" (vdata @-> ret set_repr) @@ fun v -> 
   tag_int_set v.out_edges

let () = define "vdata_in_indices" (vdata @-> ret set_repr) @@ fun v -> 
   tag_int_set v.in_indices

let () = define "vdata_out_indices" (vdata @-> ret set_repr) @@ fun v -> 
   tag_int_set v.out_indices

let () = define "vdata_value" (vdata @-> ret string) @@ fun v -> 
   v.value


let val_edata = Tac2dyn.Val.create (plugin_name^":edata")
let edata = repr_ext val_edata

let () = define "edata_make" (string @-> ret edata) @@ fun value -> 
   Graph.make_edata ~value:value ()

let () = define "edata_make_from" 
   (list int @-> list int @-> string @-> ret edata) @@ 
   fun s t value -> Graph.make_edata ~s:s ~t:t ~value:value ()

let edata_equal (ed : Graph.edata) (ed' : Graph.edata) : bool = 
   List.equal Int.equal ed.s ed'.s &&
   List.equal Int.equal ed.t ed'.t &&
   String.equal ed.value ed'.value

let () = define "edata_equal" (edata @-> edata @-> ret bool) @@ edata_equal

let () = define "edata_source" (edata @-> ret (list int)) @@ fun e -> e.s

let () = define "edata_target" (edata @-> ret (list int)) @@ fun e -> e.t

let () = define "edata_value" (edata @-> ret string) @@ fun e -> e.value

let val_graph = Tac2dyn.Val.create (plugin_name^":graph")
let graph = repr_ext val_graph

let () = define "graph_make" (unit @-> ret graph) @@ Graph.make

let () = define "graph_make_from" 
   (map_repr @-> map_repr @-> list int @-> list int @-> int @-> int @-> ret graph) @@ 
   fun v e inputs outputs vindex eindex -> {
      vdata = untag_int_map vdata v;
      edata = untag_int_map edata e;
      inputs = inputs;
      outputs = outputs;
      vindex = vindex;
      eindex = eindex;
   }

let graph_equal (g : Graph.t) (g' : Graph.t) : bool = 
   Graph.NMap.equal vdata_equal g.vdata g'.vdata &&
   Graph.NMap.equal edata_equal g.edata g'.edata &&
   List.equal Int.equal g.inputs g'.inputs && 
   List.equal Int.equal g.outputs g'.outputs

let () = define "graph_equal" (graph @-> graph @-> ret bool) @@ graph_equal

let () = define "graph_vdata" (graph @-> ret map_repr) @@ 
   fun g -> tag_int_map vdata g.vdata
let () = define "graph_edata" (graph @-> ret map_repr) @@ 
   fun g -> tag_int_map edata g.edata
let () = define "graph_inputs" (graph @-> ret (list int)) @@ fun g -> g.inputs
let () = define "graph_outputs" (graph @-> ret (list int)) @@ fun g -> g.outputs
let () = define "graph_vindex" (graph @-> ret int) @@ fun g -> g.vindex
let () = define "graph_eindex" (graph @-> ret int) @@ fun g -> g.eindex

let () = define "graph_string_of_edata" (edata @-> ret string) @@ Graph.string_of_edata


let () = define "graph_vertices" (graph @-> ret (list int)) @@ Graph.vertices
let () = define "graph_edges" (graph @-> ret (list int)) @@ Graph.edges

let () = define "graph_num_vertices" (graph @-> ret int) @@ Graph.num_vertices
let () = define "graph_num_edges" (graph @-> ret int) @@ Graph.num_edges

let () = define "graph_vertex_data" (graph @-> int @-> ret vdata) @@ 
   Graph.vertex_data
let () = define "graph_edge_data" (graph @-> int @-> ret edata) @@ 
   Graph.edge_data

let () = define "graph_in_edges" (graph @-> int @-> ret set_repr) @@ 
   fun g v -> tag_int_set (Graph.in_edges g v)
let () = define "graph_out_edges" (graph @-> int @-> ret set_repr) @@ 
   fun g v -> tag_int_set (Graph.out_edges g v)

let () = define "graph_source" (graph @-> int @-> ret (list int)) @@ 
   fun g v -> Graph.source g v
let () = define "graph_target" (graph @-> int @-> ret (list int)) @@ 
   fun g v -> Graph.target g v

let () = define "graph_add_vertex" 
   (option string @-> option int @-> graph @-> ret (pair graph int)) @@ 
   fun value name g ->
   let value = match value with | Some value -> value | None -> "" in 
   let name = match name with | Some name -> name | None -> -1 in 
   Graph.add_vertex ~value:value ~name:name g


let () = define "graph_add_edge" (option string @-> option int 
   @-> list int @-> list int @-> graph @-> ret (pair graph int)) @@ 
   fun value name s t g ->
   let value = match value with | Some value -> value | None -> "" in 
   let name = match name with | Some name -> name | None -> -1 in 
   Graph.add_edge ~value:value ~name:name s t g

let () = define "graph_set_inputs" (list int @-> graph @-> ret graph) @@ 
   Graph.set_inputs

let () = define "graph_set_outputs" (list int @-> graph @-> ret graph) @@ 
   Graph.set_outputs

let () = define "graph_is_input" (graph @-> int @-> ret bool) @@ Graph.is_input
let () = define "graph_is_output" (graph @-> int @-> ret bool) @@ Graph.is_output
let () = define "graph_is_boundary" (graph @-> int @-> ret bool) @@ Graph.is_boundary






let () = define "match_get_debug_match" (unit @-> ret bool) @@ fun () ->
   !Match.debug_match

let () = define "match_set_debug_match" (bool @-> ret unit) @@ fun b ->
   Match.debug_match := b

let val_match = Tac2dyn.Val.create (plugin_name^":match")
let match_t = repr_ext val_match

let () = define "match_make" (graph @-> graph @-> ret match_t) @@ 
   Match.make_match

let () = define "match_make_from" (graph @-> graph @-> 
   map_repr @-> set_repr @-> map_repr @-> set_repr @-> ret match_t) @@
   fun domain codomain vertex_map vertex_image edge_map edge_image -> {
      domain = domain;
      codomain = codomain;
      vertex_map = untag_int_map int vertex_map;
      vertex_image = untag_int_set vertex_image;
      edge_map = untag_int_map int edge_map;
      edge_image = untag_int_set edge_image;
   }

let match_equal (m : Match.t) (m' : Match.t) : bool = 
   let open Match in 
   graph_equal m.domain m'.domain &&
   graph_equal m.codomain m'.codomain &&
   NMap.equal Int.equal m.vertex_map m'.vertex_map &&
   NSet.equal m.vertex_image m'.vertex_image &&
   NMap.equal Int.equal m.edge_map m'.edge_map &&
   NSet.equal m.edge_image m'.edge_image

let () = define "match_equal" (match_t @-> match_t @-> ret bool) @@ match_equal

let () = define "match_domain" (match_t @-> ret graph) @@
   fun m -> m.domain
let () = define "match_codomain" (match_t @-> ret graph) @@
   fun m -> m.codomain
let () = define "match_vertex_map" (match_t @-> ret map_repr) @@
   fun m -> tag_int_map int m.vertex_map
let () = define "match_vertex_image" (match_t @-> ret set_repr) @@
   fun m -> tag_int_set m.vertex_image
let () = define "match_edge_map" (match_t @-> ret map_repr) @@
   fun m -> tag_int_map int m.edge_map
let () = define "match_edge_image" (match_t @-> ret set_repr) @@
   fun m -> tag_int_set m.edge_image

let () = define "match_try_add_vertex" 
   (int @-> int @-> match_t @-> ret (option match_t)) @@ 
   Match.try_add_vertex

let () = define "match_try_add_edge" 
   (int @-> int @-> match_t @-> ret (option match_t)) @@ 
   Match.try_add_edge

let () = define "match_domain_neighbourhood_mapped" 
   (match_t @-> int @-> ret bool) @@ Match.domain_neighbourhood_mapped

let () = define "match_map_scalars" 
   (match_t @-> ret (option match_t)) @@ Match.map_scalars

let () = define "match_more" 
   (match_t @-> ret (list match_t)) @@ Match.more


let () = define "match_is_total" 
   (match_t @-> ret bool) @@ Match.is_total
let () = define "match_is_surjective" 
   (match_t @-> ret bool) @@ Match.is_surjective
let () = define "match_is_injective" 
   (match_t @-> ret bool) @@ Match.is_injective

let () = define "match_make_match_sequence" 
   (graph @-> graph @-> option match_t @-> ret (list match_t)) @@
   fun domain codomain initial_match_opt ->
   (Match.make_match_sequence domain codomain initial_match_opt).match_stack

let () = define "match_next_match" 
   (list match_t @-> ret (option (pair match_t (list match_t)))) @@
   fun matches ->
   match Match.next_match {match_stack = matches} with 
   | Some (m, s) -> Some (m, s.match_stack)
   | None -> None


let () = define "match_seq_to_list" 
   (list match_t @-> ret (list match_t)) @@
   fun matches ->
   Match.seq_to_list {match_stack = matches}

let () = define "match_match_graph" 
   (graph @-> graph @-> ret (list match_t)) @@ 
   fun domain codomain -> 
      (Match.match_graph domain codomain).match_stack

let () = define "match_count" 
   (list match_t @-> ret int) @@ fun ms -> 
   Match.count {match_stack = ms}

let () = define "match_find_iso" 
   (graph @-> graph @-> ret (option match_t)) @@ 
   Match.find_iso




(* Printing  *)


let pr_int_set ?(sep=Pp.pr_comma) s = 
   let open Pp in 
   let body = prlist_with_sep sep int (NSet.elements s) in 
   str "{" ++ body ++ str "}"

let pr_colon () = let open Pp in str ":" ++ spc()

let pr_int_map ?(sep=Pp.pr_comma) ?(msep=pr_colon) pr m = 
   let open Pp in 
   let body = prlist_with_sep sep 
      (fun (i, v) -> int i ++ msep() ++ pr v) (NMap.bindings m) in 
   str "{" ++ body ++ str "}"

let prlist_with_brackets ?(sep=Pp.pr_comma) pr l = 
   let open Pp in 
   let body = prlist_with_sep sep pr l in 
   str "[" ++ body ++ str "]"

let pr_vdata (vd : Graph.vdata) = 
   let open Pp in 
   hov 2 @@ str "VData with" ++ spc() ++ str "{" ++ 
      str "value = " ++ quote (str vd.value) ++ pr_comma() ++
      str "in_edges = " ++ pr_int_set vd.in_edges ++ pr_comma() ++
      str "out_edges = " ++ pr_int_set vd.out_edges ++ pr_comma() ++
      str "in_indices = " ++ pr_int_set vd.in_indices ++ pr_comma() ++
      str "out_indices = " ++ pr_int_set vd.out_indices ++ str "}"

let pr_edata (ed : Graph.edata) = 
   let open Pp in 
   hov 2 @@ str "EData with" ++ spc() ++ str "{" ++ 
      str "value = " ++ quote (str ed.value) ++ pr_comma() ++
      str "s = " ++ prlist_with_brackets int ed.s ++ pr_comma() ++
      str "t = " ++ prlist_with_brackets int ed.t ++ str "}"
   

let pr_edata_nice (ed : Graph.edata) = 
   let open Pp in 
   hov 2 @@ quote (str ed.value) ++ spc() ++ str "(" ++
      (h @@ prlist_with_brackets int ed.s ++ spc() ++ str "->" 
         ++ spc() ++ prlist_with_brackets int ed.t) ++ str ")"

let pr_edge_to_parse (e : int) (ed : Graph.edata) = 
   let open Pp in 
   hov 2 @@ str ed.value ++ spc() ++ 
      str "(" ++ int e ++ str ")" ++ spc() ++ pr_colon() ++
      prlist_with_sep pr_comma int ed.s ++ spc() ++ str "->" ++ spc() ++
      prlist_with_sep pr_comma int ed.t

let pr_graph (g : Graph.t) = 
   let open Pp in 
   v 2 @@ str "Graph with" ++ spc() ++
      (v 2 @@ str "Vertices:" ++ spc () ++ 
         (hov 2 @@ pr_int_map (fun (vd : Graph.vdata) -> 
            quote (str vd.value)) g.vdata)) ++ spc() ++
      (v 2 @@ str "Edges:" ++ spc () ++ 
         (hov 2 @@ pr_int_map (fun (ed : Graph.edata) -> 
            quote (str ed.value)) g.edata)) ++ spc() ++ 
      (hov 2 @@ str "Inputs:" ++ spc () ++ 
         prlist_with_brackets int g.inputs) ++ spc() ++
      (hov 2 @@ str "Outputs:" ++ spc () ++ 
         prlist_with_brackets int g.outputs)

let pr_graph_full (g : Graph.t) = 
   let open Pp in 
   v 2 @@ str "Graph with" ++ spc() ++
      (v 2 @@ str "Vertices:" ++ spc () ++ 
         (hov 2 @@ pr_int_map (fun (vd : Graph.vdata) -> 
            quote (str vd.value)) g.vdata)) ++ spc() ++
      (v 2 @@ str "Edges:" ++ spc () ++ 
         (hov 2 @@ pr_int_map (fun (ed : Graph.edata) -> 
             (pr_edata_nice ed)) g.edata)) ++ spc() ++ 
      (hov 2 @@ str "Inputs:" ++ spc () ++ 
         prlist_with_brackets int g.inputs) ++ spc() ++
      (hov 2 @@ str "Outputs:" ++ spc () ++ 
         prlist_with_brackets int g.outputs)

(* FIXME TODO: Move *)
let vdata_is_orphan (vd : Graph.vdata) : bool =
   Graph.NSet.is_empty vd.in_edges &&
   Graph.NSet.is_empty vd.out_edges &&
   Graph.NSet.is_empty vd.in_indices &&
   Graph.NSet.is_empty vd.out_indices

let pr_graph_nice (g : Graph.t) = 
   let orphans = List.filter_map (fun (v, vd) -> 
      if vdata_is_orphan vd then Some v else None) (Graph.NMap.bindings g.vdata) in 
   let open Pp in 
   hov 2 @@ str "!Graph" ++ spc() ++ 
      prlist_with_sep pr_comma int g.inputs  ++ spc() ++ str "->" ++ spc() ++
      prlist_with_sep pr_comma int g.outputs ++ spc() ++ str ":"  ++ spc() ++ 

      prlist_with_sep pr_semicolon (fun (e, ed) -> pr_edge_to_parse e ed)
         (Graph.NMap.bindings g.edata) ++

      if CList.is_empty orphans then spc() else 
         spc() ++ str "and" ++ spc() ++ prlist_with_sep pr_comma int orphans


let pr_match ?(domain=false) ?(codomain=false) (m : Match.t) = 
   let open Pp in 
   v 2 @@ str "Match with" ++ spc() ++ str "{" ++ 
      (if domain then hov 2 @@ str "domain =" ++ spc() 
            ++ pr_graph m.domain ++ pr_comma()
      else str "") ++ 
      (if codomain then hov 2 @@ str "codomain =" ++ spc() 
            ++ pr_graph m.codomain ++ pr_comma()
      else str "") ++ 
      (hov 2 @@ str "vertex_map =" ++ spc() ++ 
         pr_int_map int ~msep:(fun ()->str "->" ++ spc()) 
            m.vertex_map) ++ pr_comma() ++ 
      (hov 2 @@ str "edge_map =" ++ spc() ++ 
         pr_int_map int ~msep:(fun ()->str "->" ++ spc())
            m.edge_map) ++ pr_comma() ++ str "}"

let pr_match_nice (m : Match.t) = 
   let open Graph in 
   let open Pp in
   let edge_verts = List.fold_right (fun e vs -> 
      let ed = edge_data m.domain e in 
      NSet.union (NSet.of_list (ed.s @ ed.t)) vs) 
      (NSet.elements (NMap.domain m.edge_map)) NSet.empty in 
   let mapped_verts = NMap.domain m.vertex_map in 
   let orphans = CList.filter (fun v -> 
      not (NSet.mem v edge_verts) && NSet.mem v mapped_verts) 
      (vertices m.domain) in 
   let pr_item name idx = if name = ""
      then int idx
      else int idx ++ spc() ++ str "(" ++ str name ++ str ")" in

   hov 2 @@ str "!Match" ++ spc() ++ str "mapping" ++ spc() ++ 
      prlist_with_sep pr_comma (fun (e, e') -> 
         let ed = Graph.edge_data m.domain e in 
         let ed' = Graph.edge_data m.codomain e' in 
         pr_item ed.value e ++ spc() ++ str "->" ++ spc() ++ 
         pr_item ed'.value e')
         (NMap.bindings m.edge_map) ++ 
   if CList.is_empty orphans then spc() else 
      spc() ++ str "and" ++ spc() ++ 
      prlist_with_sep pr_comma (fun v -> 
         let v' = NMap.find v m.vertex_map in 
         let vd = Graph.vertex_data m.domain v in 
         let vd' = Graph.vertex_data m.codomain v' in 
         pr_item vd.value v ++ spc() ++ str "->" ++ spc() ++ 
         pr_item vd'.value v')
         orphans


let pr_match_nice_full (m : Match.t) = 
   let open Graph in 
   let open Pp in
   let edge_verts = List.fold_right (fun e vs -> 
      let ed = edge_data m.domain e in 
      NSet.union (NSet.of_list (ed.s @ ed.t)) vs) 
      (NSet.elements (NMap.domain m.edge_map)) NSet.empty in 
   let mapped_verts = NMap.domain m.vertex_map in 
   let orphans = CList.filter (fun v -> 
      not (NSet.mem v edge_verts) && NSet.mem v mapped_verts) 
      (vertices m.domain) in 
   let pr_item name idx = if name = ""
      then int idx
      else int idx ++ spc() ++ str "(" ++ str name ++ str ")" in

   hov 2 @@ str "!Match" ++ spc() ++ 
   str "(" ++ pr_graph_nice m.domain ++ str ")" ++
   spc() ++ str "with" ++ spc() ++
   str "(" ++ pr_graph_nice m.codomain ++ str ")" ++
   spc() ++ str "mapping" ++ spc() ++ 
      prlist_with_sep pr_comma (fun (e, e') -> 
         let ed = Graph.edge_data m.domain e in 
         let ed' = Graph.edge_data m.codomain e' in 
         pr_item ed.value e ++ spc() ++ str "->" ++ spc() ++ 
         pr_item ed'.value e')
         (NMap.bindings m.edge_map) ++ 
   if CList.is_empty orphans then spc() else 
      spc() ++ str "and" ++ spc() ++ 
      prlist_with_sep pr_comma (fun v -> 
         let v' = NMap.find v m.vertex_map in 
         let vd = Graph.vertex_data m.domain v in 
         let vd' = Graph.vertex_data m.codomain v' in 
         pr_item vd.value v ++ spc() ++ str "->" ++ spc() ++ 
         pr_item vd'.value v')
         orphans

let _mk_pr r f = fun _ _ v _ -> f (repr_to r v)

let pr_vdata' _env _sigma v _tys =
  (* assert (CList.is_empty tys);  *)
  let vd = repr_to vdata v in
  pr_vdata vd

let pr_edata' _env _sigma v _tys =
  (* assert (CList.is_empty tys);  *)
  let ed = repr_to edata v in
  pr_edata ed

let pr_graph' _env _sigma v _tys =
  (* assert (CList.is_empty tys);  *)
  let g = repr_to graph v in
  pr_graph g

let pr_match' _env _sigma v _tys =
  (* assert (CList.is_empty tys);  *)
  let m = repr_to match_t v in
  pr_match m


let base_module = ["HypercamlInterface" ; "HyperOCM"]

let vdata_module_name = ModPath.MPfile (DirPath.make @@ 
   List.map Id.of_string (["VData"] @ base_module))
let edata_module_name = ModPath.MPfile (DirPath.make @@ 
   List.map Id.of_string (["EData"] @ base_module))
let graph_module_name = ModPath.MPfile (DirPath.make @@ 
   List.map Id.of_string (["Graph"] @ base_module))
let match_module_name = ModPath.MPfile (DirPath.make @@ 
   List.map Id.of_string (["Match"] @ base_module))

let t_label = Label.of_id @@ Id.of_string "t"

let vdata_type_name = KerName.make vdata_module_name t_label
let edata_type_name = KerName.make edata_module_name t_label
let graph_type_name = KerName.make graph_module_name t_label
let match_type_name = KerName.make match_module_name t_label

(* I don't know why this doesn't work? *)
let () = Tac2print.register_val_printer vdata_type_name { 
   val_printer = (* mk_pr vdata *) pr_vdata' }
let () = Tac2print.register_val_printer edata_type_name { 
   val_printer = (* mk_pr edata *) pr_edata' }
let () = Tac2print.register_val_printer graph_type_name { 
   val_printer = (* mk_pr graph *) pr_graph' }
let () = Tac2print.register_val_printer match_type_name { 
   val_printer = (* mk_pr match_t *) pr_match' }

let () = define "print_vdata" (vdata @-> ret pp) pr_vdata
let () = define "print_edata" (edata @-> ret pp) pr_edata
let () = define "print_edata_nice" (edata @-> ret pp) pr_edata_nice
let () = define "print_edge_to_parse" (int @-> edata @-> ret pp) pr_edge_to_parse
let () = define "print_graph" (graph @-> ret pp) pr_graph
let () = define "print_graph_full" (graph @-> ret pp) pr_graph_full
let () = define "print_graph_nice" (graph @-> ret pp) pr_graph_nice
let () = define "print_match" (match_t @-> ret pp) pr_match
let () = define "print_match_nice" (match_t @-> ret pp) pr_match_nice
let () = define "print_match_nice_full" (match_t @-> ret pp) pr_match_nice_full;



(* open Yojson

let _graph_of_json (json : Basic.t) : Graph.t =
   let open Yojson.Basic.Util in 
   let g = Graph.make () in 
   let _vertices = json |> member "vertices" |> to_assoc in 
   g *)
   (* let g = List.fold_right
      (fun ) *)

