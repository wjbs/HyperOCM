(** Matching of a graph into another. *)

open Printf

exception Match_error of string

(* Set structures for vertex/edge mappings *)
module NSet = Graph.NSet
module NMap = Graph.NMap


(* Enable/disable debug output *)

let debug_match = ref false

let match_log s =
  if !debug_match then printf "%s\n%!" s

(* Type representing a match between two graphs *)
type t = {
  domain: Graph.t;
  codomain: Graph.t;
  vertex_map: int NMap.t;
  vertex_image: NSet.t;
  edge_map: int NMap.t;
  edge_image: NSet.t;
}

(* Create a new match between two graphs *)
let make_match domain codomain = {
  domain;
  codomain;
  vertex_map = NMap.empty;
  vertex_image = NSet.empty;
  edge_map = NMap.empty;
  edge_image = NSet.empty;
}

(* Copy a match *)
let copy_match m = {
  domain = m.domain;
  codomain = m.codomain;
  vertex_map = m.vertex_map;
  vertex_image = m.vertex_image;
  edge_map = m.edge_map;
  edge_image = m.edge_image;
}

(* String representation of a match *)
let string_of_match m =
  let vertex_map_str = 
    NMap.bindings m.vertex_map
    |> List.map (fun (k, v) -> sprintf "%d->%d" k v)
    |> String.concat "; "
  in
  let edge_map_str =
    NMap.bindings m.edge_map
    |> List.map (fun (k, v) -> sprintf "%d->%d" k v)
    |> String.concat "; "
  in
  sprintf "\tVertex map: [%s]\n\tEdge map: [%s]" vertex_map_str edge_map_str

(* Try to add a vertex mapping to a match *)
let try_add_vertex domain_vertex codomain_vertex m =
  match_log (sprintf "Trying to add vertex %d -> %d to match:" domain_vertex codomain_vertex);
  match_log (string_of_match m);
  
  (* Check that vertex values match *)
  let domain_value = (Graph.vertex_data m.domain domain_vertex).value in
  let codomain_value = (Graph.vertex_data m.codomain codomain_vertex).value in
  if domain_value <> codomain_value then (
    match_log (sprintf "Vertex failed: values %s != %s" domain_value codomain_value);
    None
  ) else
    (* If the vertex is already mapped, check consistency *)
    if NMap.mem domain_vertex m.vertex_map then
      let existing_mapping = NMap.find domain_vertex m.vertex_map in
      match_log (sprintf "Vertex already mapped to %d." existing_mapping);
      if existing_mapping = codomain_vertex then
        Some m
      else
        None
    else
    (* Ensure non-boundary vertices in domain are not mapped to boundary vertices in codomain *)
    if Graph.is_boundary m.codomain codomain_vertex && not (Graph.is_boundary m.domain domain_vertex) then (
      match_log "Vertex failed: codomain vertex is boundary but domain vertex is not.";
      None
    ) else
      (* Check injectivity constraints *)
      if NSet.mem codomain_vertex m.vertex_image then (
        (* Non-injective mapping is only allowed on boundary vertices *)
        if not (Graph.is_boundary m.domain domain_vertex) then (
          match_log "Vertex failed: non-injective on interior vertex.";
          None
        ) else
          (* Check that all vertices already mapped to this codomain vertex are boundary *)
          let all_boundary = NMap.for_all (fun mapped_vertex image_vertex ->
            if image_vertex = codomain_vertex then
              Graph.is_boundary m.domain mapped_vertex
            else
              true
          ) m.vertex_map in
          if not all_boundary then (
            match_log "Vertex failed: non-injective on interior vertex.";
            None
          ) else (
            (* Add the mapping *)
            let new_match = {
              m with
              vertex_map = NMap.add domain_vertex codomain_vertex m.vertex_map;
              vertex_image = NSet.add codomain_vertex m.vertex_image;
            } in
            (* Check gluing conditions for non-boundary vertices *)
            if not (Graph.is_boundary m.domain domain_vertex) then (
              let domain_in_edges = Graph.in_edges m.domain domain_vertex |> NSet.cardinal in
              let codomain_in_edges = Graph.in_edges m.codomain codomain_vertex |> NSet.cardinal in
              let domain_out_edges = Graph.out_edges m.domain domain_vertex |> NSet.cardinal in
              let codomain_out_edges = Graph.out_edges m.codomain codomain_vertex |> NSet.cardinal in
              if domain_in_edges <> codomain_in_edges then (
                match_log "Vertex failed: in_edges cannot satisfy gluing conditions.";
                None
              ) else if domain_out_edges <> codomain_out_edges then (
                match_log "Vertex failed: out_edges cannot satisfy gluing conditions.";
                None
              ) else (
                match_log "Vertex success.";
                Some new_match
              )
            ) else (
              match_log "Vertex success.";
              Some new_match
            )
          )
      ) else (
        (* Add the mapping *)
        let new_match = {
          m with
          vertex_map = NMap.add domain_vertex codomain_vertex m.vertex_map;
          vertex_image = NSet.add codomain_vertex m.vertex_image;
        } in
        (* Check gluing conditions for non-boundary vertices *)
        if not (Graph.is_boundary m.domain domain_vertex) then (
          let domain_in_edges = Graph.in_edges m.domain domain_vertex |> NSet.cardinal in
          let codomain_in_edges = Graph.in_edges m.codomain codomain_vertex |> NSet.cardinal in
          let domain_out_edges = Graph.out_edges m.domain domain_vertex |> NSet.cardinal in
          let codomain_out_edges = Graph.out_edges m.codomain codomain_vertex |> NSet.cardinal in
          if domain_in_edges <> codomain_in_edges then (
            match_log "Vertex failed: in_edges cannot satisfy gluing conditions.";
            None
          ) else if domain_out_edges <> codomain_out_edges then (
            match_log "Vertex failed: out_edges cannot satisfy gluing conditions.";
            None
          ) else (
            match_log "Vertex success.";
            Some new_match
          )
        ) else (
          match_log "Vertex success.";
          Some new_match
        )
      )

(* Try to add an edge mapping to a match *)
let try_add_edge domain_edge codomain_edge m =
  match_log (sprintf "Trying to add edge %d -> %d to match:" domain_edge codomain_edge);
  match_log (string_of_match m);
  
  (* Check that edge values match *)
  let domain_value = (Graph.edge_data m.domain domain_edge).value in
  let codomain_value = (Graph.edge_data m.codomain codomain_edge).value in
  if domain_value <> codomain_value then (
    match_log (sprintf "Edge failed: values %s != %s" domain_value codomain_value);
    None
  ) else
    (* Check injectivity of edge map *)
    if NSet.mem codomain_edge m.edge_image then (
      match_log "Edge failed: the map would become non-injective.";
      None
    ) else
      (* Add the edge mapping *)
      let new_match = {
        m with
        edge_map = NMap.add domain_edge codomain_edge m.edge_map;
        edge_image = NSet.add codomain_edge m.edge_image;
      } in
      
      (* Check vertex map consistency *)
      let domain_sources = Graph.source m.domain domain_edge in
      let codomain_sources = Graph.source m.codomain codomain_edge in
      let domain_targets = Graph.target m.domain domain_edge in
      let codomain_targets = Graph.target m.codomain codomain_edge in
      let vertices_to_check = List.combine (domain_sources @ domain_targets) (codomain_sources @ codomain_targets) in
      
      let rec check_vertices acc_match = function
        | [] -> Some acc_match
        | (domain_vertex, codomain_vertex) :: rest ->
            if NMap.mem domain_vertex acc_match.vertex_map then
              (* Check consistency with existing mapping *)
              let existing_mapping = NMap.find domain_vertex acc_match.vertex_map in
              if existing_mapping <> codomain_vertex then (
                match_log "Edge failed: inconsistent with previously mapped vertex.";
                None
              ) else
                check_vertices acc_match rest
            else
              (* Try to add new vertex mapping *)
              match try_add_vertex domain_vertex codomain_vertex acc_match with
              | None ->
                  match_log "Edge failed: couldn't add a source or target vertex.";
                  None
              | Some updated_match ->
                  check_vertices updated_match rest
      in
      
      match check_vertices new_match vertices_to_check with
      | None -> None
      | Some final_match ->
          match_log "Edge success.";
          Some final_match

(* Check if all adjacent edges of a domain vertex are mapped *)
let domain_neighbourhood_mapped m vertex =
  let in_edges = Graph.in_edges m.domain vertex in
  let out_edges = Graph.out_edges m.domain vertex in
  NSet.for_all (fun e -> NMap.mem e m.edge_map) in_edges &&
  NSet.for_all (fun e -> NMap.mem e m.edge_map) out_edges

(* Try to map all scalars (0 -> 0 edges) *)
let map_scalars m =
  (* Find all scalars in the codomain *)
  let codomain_scalars = 
    Graph.edges m.codomain
    |> List.filter (fun edge ->
        let edge_data = Graph.edge_data m.codomain edge in
        List.length edge_data.s = 0 && List.length edge_data.t = 0)
    |> List.map (fun edge ->
        let edge_data = Graph.edge_data m.codomain edge in
        (edge, edge_data.value))
  in
  
  (* Find all scalars in the domain and try to map them *)
  let domain_scalars = 
    Graph.edges m.domain
    |> List.filter (fun edge ->
        let edge_data = Graph.edge_data m.domain edge in
        List.length edge_data.s = 0 && List.length edge_data.t = 0)
  in
  
  let rec map_domain_scalars acc_match available_cod_scalars = function
    | [] -> Some acc_match
    | domain_edge :: rest_domain ->
        let domain_value = (Graph.edge_data m.domain domain_edge).value in
        match_log (sprintf "Trying to map scalar edge %d" domain_edge);
        
        (* Find a matching codomain scalar *)
        let rec find_matching_scalar acc_available = function
          | [] ->
              match_log (sprintf "Match failed: could not map scalar edge %d." domain_edge);
              None
          | (codomain_scalar, value) :: rest_available ->
              if value = domain_value then
                (* Map the domain scalar to this codomain scalar *)
                let new_match = {
                  acc_match with
                  edge_map = NMap.add domain_edge codomain_scalar acc_match.edge_map;
                  edge_image = NSet.add codomain_scalar acc_match.edge_image;
                } in
                match_log (sprintf "Successfully mapped scalar %d -> %d" domain_edge codomain_scalar);
                map_domain_scalars new_match (acc_available @ rest_available) rest_domain
              else
                find_matching_scalar (acc_available @ [(codomain_scalar, value)]) rest_available
        in
        find_matching_scalar [] available_cod_scalars
  in
  
  map_domain_scalars m codomain_scalars domain_scalars

(* Get all matches that extend a given match by one vertex or edge *)
let more m =
  let extended_matches = ref [] in
  
  (* Try to add edges adjacent to already matched vertices *)
  let matched_vertices = NMap.bindings m.vertex_map in
  let rec try_vertex_edges = function
    | [] -> ()
    | (domain_vertex, codomain_vertex) :: rest ->
        if domain_neighbourhood_mapped m domain_vertex then
          try_vertex_edges rest
        else (
          (* Try to extend by mapping adjacent in-edges *)
          let domain_in_edges = Graph.in_edges m.domain domain_vertex |> NSet.elements in
          let codomain_in_edges = Graph.in_edges m.codomain codomain_vertex |> NSet.elements in
          let unmapped_in_edges = List.filter (fun e -> not (NMap.mem e m.edge_map)) domain_in_edges in
          
          match unmapped_in_edges with
          | edge :: _ ->
              List.iter (fun codomain_edge ->
                let potential_match = copy_match m in
                match try_add_edge edge codomain_edge potential_match with
                | Some new_match -> extended_matches := new_match :: !extended_matches
                | None -> ()
              ) codomain_in_edges
          | [] ->
              (* Try to extend by mapping adjacent out-edges *)
              let domain_out_edges = Graph.out_edges m.domain domain_vertex |> NSet.elements in
              let codomain_out_edges = Graph.out_edges m.codomain codomain_vertex |> NSet.elements in
              let unmapped_out_edges = List.filter (fun e -> not (NMap.mem e m.edge_map)) domain_out_edges in
              
              match unmapped_out_edges with
              | edge :: _ ->
                  List.iter (fun codomain_edge ->
                    let potential_match = copy_match m in
                    match try_add_edge edge codomain_edge potential_match with
                    | Some new_match -> extended_matches := new_match :: !extended_matches
                    | None -> ()
                  ) codomain_out_edges
              | [] -> try_vertex_edges rest
        )
  in
  
  try_vertex_edges matched_vertices;
  
  (* If no edge extensions found, try to match unmatched vertices *)
  if !extended_matches = [] then (
    let domain_vertices = Graph.vertices m.domain in
    let codomain_vertices = Graph.vertices m.codomain in
    let unmatched_vertices = List.filter (fun v -> not (NMap.mem v m.vertex_map)) domain_vertices in
    
    match unmatched_vertices with
    | domain_vertex :: _ ->
        List.iter (fun codomain_vertex ->
          let potential_match = copy_match m in
          match try_add_vertex domain_vertex codomain_vertex potential_match with
          | Some new_match -> extended_matches := new_match :: !extended_matches
          | None -> ()
        ) codomain_vertices
    | [] -> ()
  );
  
  !extended_matches

(* Check if a match is total (all domain vertices and edges mapped) *)
let is_total m =
  NMap.cardinal m.vertex_map = Graph.num_vertices m.domain &&
  NMap.cardinal m.edge_map = Graph.num_edges m.domain

(* Check if a match is surjective *)
let is_surjective m =
  NSet.cardinal m.vertex_image = Graph.num_vertices m.codomain &&
  NSet.cardinal m.edge_image = Graph.num_edges m.codomain

(* Check if a match is injective *)
let is_injective m =
  (* Edge map is always injective, only need to check vertex map *)
  NMap.cardinal m.vertex_map = NSet.cardinal m.vertex_image

(* Type representing a sequence of matches *)
type seq = {
  match_stack: t list;
}

(* Create a new match sequence *)
let make_match_sequence domain codomain initial_match_opt =
  let initial_match = match initial_match_opt with
    | Some m -> m
    | None -> make_match domain codomain
  in
  
  (* Try to map scalars in the initial match *)
  (* TODO: we should be mapping scalars in all possible ways *)
  match map_scalars initial_match with
  | Some m -> { match_stack = [m] }
  | None -> { match_stack = [] }

(* Get the next total match from a match sequence *)
let rec next_match seq =
  match seq.match_stack with
  | [] -> None
  | m :: rest ->
      let new_seq = { match_stack = rest } in
      if is_total m then (
        match_log ("got successful match:\n" ^ string_of_match m);
        Some (m, new_seq)
      ) else
        let extended_matches = more m in
        let updated_seq = { match_stack = extended_matches @ rest } in
        next_match updated_seq

(* Convert a match sequence to a list of total matches *)
let seq_to_list seq =
  let rec collect_matches acc current_seq =
    match next_match current_seq with
    | None -> List.rev acc
    | Some (m, new_seq) -> collect_matches (m :: acc) new_seq
  in
  collect_matches [] seq

(* Main function to find matches of domain into codomain *)
let match_graph domain codomain = make_match_sequence domain codomain None

let rec count seq = match next_match seq with
  | None -> 0
  | Some (_, new_seq) -> 1 + count new_seq

(* Find an isomorphism between two graphs *)
let find_iso domain_graph codomain_graph =
  let domain_inputs = Graph.inputs domain_graph in
  let domain_outputs = Graph.outputs domain_graph in
  let codomain_inputs = Graph.inputs codomain_graph in
  let codomain_outputs = Graph.outputs codomain_graph in
  
  (* Try to create initial match mapping boundary vertices *)
  let initial_match = make_match domain_graph codomain_graph in
  
  let rec add_input_mappings acc_match = function
    | ([], []) -> Some acc_match
    | (d_input :: d_rest, c_input :: c_rest) ->
        (match try_add_vertex d_input c_input acc_match with
         | None -> None
         | Some new_match -> add_input_mappings new_match (d_rest, c_rest))
    | _ -> None (* Mismatched input lengths *)
  in
  
  let rec add_output_mappings acc_match = function
    | ([], []) -> Some acc_match
    | (d_output :: d_rest, c_output :: c_rest) ->
        (match try_add_vertex d_output c_output acc_match with
         | None -> None
         | Some new_match -> add_output_mappings new_match (d_rest, c_rest))
    | _ -> None (* Mismatched output lengths *)
  in
  
  match add_input_mappings initial_match (domain_inputs, codomain_inputs) with
  | None -> None
  | Some match_with_inputs ->
      match add_output_mappings match_with_inputs (domain_outputs, codomain_outputs) with
      | None -> None
      | Some initial_match_complete ->
          let seq = make_match_sequence domain_graph codomain_graph (Some initial_match_complete) in
          let rec find_surjective_match current_seq =
            match next_match current_seq with
            | None -> None
            | Some (m, new_seq) ->
                if is_surjective m then Some m
                else find_surjective_match new_seq
          in
          find_surjective_match seq
