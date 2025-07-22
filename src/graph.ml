open Printf

exception Graph_error of string

(* Set and map structures for vertex/edge names (i.e. ints) *)
module NSet = Int.Set
module NMap = Int.Map

(* Data associated with a single vertex *)
type vdata = {
  in_edges: NSet.t;
  (* Integer names of input hyperedges of this vertex *)
  out_edges: NSet.t;
  (* Integer names of output hyperedges of this vertex *)
  in_indices: NSet.t;
  (* Indices (if any) where this vertex occurs in the input lists of the hypergraph *)
  out_indices: NSet.t;
  (* Indices (if any) where this vertex occurs in the output lists of the hypergraph *)
  value: string;
  (* A field that can hold arbitrary data attached to a vertex *)
}

(* Create a new VData instance *)
let make_vdata ?(value = "") () = {
  in_edges = NSet.empty;
  out_edges = NSet.empty;
  in_indices = NSet.empty;
  out_indices = NSet.empty;
  value;
}

(* Data associated with a single edge *)
type edata = {
  s: int list;
  (* The source vertex list of the hyperedge *)
  t: int list;
  (* The target vertex list of the hyperedge *)
  value: string;
  (* A field that can hold some data attached to an edge *)
}

(* Create a new EData instance *)
let make_edata ?(s = []) ?(t = []) ?(value = "") () = {
  s; t; value;
}

(* String representation of an edge *)
let string_of_edata edata =
  sprintf "Edge: %s ([%s], [%s])" 
    edata.value
    (String.concat "; " (List.map string_of_int edata.s))
    (String.concat "; " (List.map string_of_int edata.t))

(* A hypergraph with boundaries *)
type t = {
  vdata: vdata NMap.t;
  (* Mapping from vertex names to data *)
  edata: edata NMap.t;
  (* Mapping from edge names to data *)
  inputs: int list;
  (* List of input vertex names *)
  outputs: int list;
  (* List of output vertex names *)
  vindex: int;
  (* Next available vertex index *)
  eindex: int;
  (* Next available edge index *)
}

(* Create a new empty graph *)
let make () = {
  vdata = NMap.empty;
  edata = NMap.empty;
  inputs = [];
  outputs = [];
  vindex = 0;
  eindex = 0;
}

(* Get list of all vertices in the graph *)
let vertices graph =
  NMap.bindings graph.vdata |> List.map fst

(* Get list of all edges in the graph *)
let edges graph =
  NMap.bindings graph.edata |> List.map fst

(* Get number of vertices in the graph *)
let num_vertices graph =
  NMap.cardinal graph.vdata

(* Get number of edges in the graph *)
let num_edges graph =
  NMap.cardinal graph.edata

(* Get vdata associated with vertex id v *)
let vertex_data graph v =
  try NMap.find v graph.vdata
  with Not_found -> raise (Graph_error (sprintf "Vertex %d not found" v))

(* Get edata associated with edge id e *)
let edge_data graph e =
  try NMap.find e graph.edata
  with Not_found -> raise (Graph_error (sprintf "Edge %d not found" e))

(* Get set of edge names for which vertex name v is a target *)
let in_edges graph v =
  (vertex_data graph v).in_edges

(* Get set of edge names for which vertex name v is a source *)
let out_edges graph v =
  (vertex_data graph v).out_edges

(* Get list of source vertex names of edge with name e *)
let source graph e =
  (edge_data graph e).s

(* Get list of target vertex names of edge with name e *)
let target graph e =
  (edge_data graph e).t

(* Add a new vertex to the graph *)
let add_vertex ?(value = "") ?(name = -1) graph =
  let v, new_vindex = 
    if name = -1 then
      graph.vindex, graph.vindex + 1
    else
      name, max name graph.vindex + 1
  in
  let new_vdata = make_vdata ~value () in
  let new_graph = {
    graph with
    vdata = graph.vdata |> NMap.add v new_vdata;
    vindex = new_vindex;
  } in
  (new_graph, v)

(* Add a new hyperedge to the graph *)
let add_edge ?(value = "") ?(name = -1) s t graph =
  let e, new_eindex = 
    if name = -1 then
      graph.eindex, graph.eindex + 1
    else
      name, max name graph.eindex + 1
  in
  let new_edata = make_edata ~s ~t ~value () in
  
  (* Update vertex data for source vertices *)
  let update_source_vertex vdata_map v =
    let vd = NMap.find v vdata_map in
    let updated_vd = { vd with out_edges = vd.out_edges |> NSet.add e } in
    vdata_map |> NMap.add v updated_vd
  in
  
  (* Update vertex data for target vertices *)
  let update_target_vertex vdata_map v =
    let vd = NMap.find v vdata_map in
    let updated_vd = { vd with in_edges = NSet.add e vd.in_edges } in
    vdata_map |> NMap.add v updated_vd
  in
  
  let updated_vdata = 
    List.fold_left update_source_vertex graph.vdata s
    |> fun vdata_map -> List.fold_left update_target_vertex vdata_map t
  in
  
  let new_graph = {
    graph with
    vdata = updated_vdata;
    edata = graph.edata |> NMap.add e new_edata;
    eindex = new_eindex;
  } in
  (new_graph, e)

(* Set the inputs of the graph *)
let set_inputs inp graph =
  (* Clear all in_indices from existing vertex data *)
  let clear_in_indices vdata_map =
    vdata_map |> NMap.map (fun vd -> { vd with in_indices = NSet.empty })
  in
  
  (* Update vertex data with new input indices *)
  let update_input_indices vdata_map =
    List.fold_left (fun acc_map (i, v) ->
      let vd = NMap.find v acc_map in
      let updated_vd = { vd with in_indices = vd.in_indices |> NSet.add i } in
      acc_map |> NMap.add v updated_vd
    ) vdata_map (List.mapi (fun i v -> (i, v)) inp)
  in
  
  let updated_vdata = 
    clear_in_indices graph.vdata
    |> update_input_indices
  in
  
  { graph with inputs = inp; vdata = updated_vdata }

(* Set the outputs of the graph *)
let set_outputs outp graph =
  (* Clear all out_indices from existing vertex data *)
  let clear_out_indices vdata_map =
    vdata_map |> NMap.map (fun vd -> { vd with out_indices = NSet.empty })
  in
  
  (* Update vertex data with new output indices *)
  let update_output_indices vdata_map =
    List.fold_left (fun acc_map (i, v) ->
      let vd = NMap.find v acc_map in
      let updated_vd = { vd with out_indices = NSet.add i vd.out_indices } in
      acc_map |> NMap.add v updated_vd
    ) vdata_map (List.mapi (fun i v -> (i, v)) outp)
  in
  
  let updated_vdata = 
    clear_out_indices graph.vdata
    |> update_output_indices
  in
  
  { graph with outputs = outp; vdata = updated_vdata }

(* Get the list of vertex ids of the graph inputs *)
let inputs graph = graph.inputs

(* Get the list of vertex ids of the graph outputs *)
let outputs graph = graph.outputs

(* Check whether vertex id v is in the graph inputs *)
let is_input graph v =
  not (NSet.is_empty (vertex_data graph v).in_indices)

(* Check whether vertex id v is in the graph outputs *)
let is_output graph v =
  not (NSet.is_empty (vertex_data graph v).out_indices)

(* Check whether vertex id v lies on the graph boundary *)
let is_boundary graph v =
  is_input graph v || is_output graph v
