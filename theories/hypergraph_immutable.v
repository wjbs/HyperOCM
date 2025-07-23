Require Import Ltac2.Init.
Require Ltac2.Ltac2.
Require Import FSetExtra.
Require PrintingExtra.
Require ListExtra.


Import ListExtra.ListForEach.

Set Default Proof Mode "Classic".

Ltac2 max (x : int) (y : int) : int :=
  if Int.lt x y then y else x.


Ltac2 Type 'a VData := {
  (* vtype : VType ; (* vtype *) *)
  in_edges : int FSet.t; (* in_edges *)
  out_edges : int FSet.t; (* out_edges *)
  in_indices : int FSet.t; (* in_indices *)
  out_indices : int FSet.t; (* out_indices *)
  vvalue : 'a option (* value *)
}.

(* Ltac2 vtype : 'a VData -> VType :=
  fun vd => vd.(vtype). *)

Ltac2 vin_edges : 'a VData -> int FSet.t :=
  fun vd => vd.(in_edges).

Ltac2 vout_edges : 'a VData -> int FSet.t :=
  fun vd => vd.(out_edges).

Ltac2 vin_indices : 'a VData -> int FSet.t :=
  fun vd => vd.(in_indices).

Ltac2 vout_indices : 'a VData -> int FSet.t :=
  fun vd => vd.(out_indices).

Ltac2 vvalue : 'a VData -> 'a option :=
  fun vd => vd.(vvalue).

Ltac2 mk_vdata : 'a option -> 'a VData := fun a => {
  in_edges := FSet.empty FSet.Tags.int_tag;
  out_edges := FSet.empty FSet.Tags.int_tag;
  in_indices := FSet.empty FSet.Tags.int_tag;
  out_indices := FSet.empty FSet.Tags.int_tag;
  vvalue := a
}.

Ltac2 mk_vdata_from ie oe ii oi : 'a option -> 'a VData := fun a => {
  in_edges := ie;
  out_edges := oe;
  in_indices := ii;
  out_indices := oi;
  vvalue := a
}.

Ltac2 vcopy (v : 'a VData) : 'a VData := {
  in_edges := v.(in_edges);
  out_edges := v.(out_edges);
  in_indices := v.(in_indices);
  out_indices := v.(out_indices);
  vvalue := v.(vvalue)
}.

Ltac2 vdata_equal (v_eq : 'a -> 'a -> bool) : 'a VData -> 'a VData -> bool :=
  fun v v' => 
  List.fold_right Bool.and [
    FSet.equal (v.(in_edges)) (v'.(in_edges));
    FSet.equal (v.(in_indices)) (v'.(in_indices));
    FSet.equal (v.(out_edges)) (v'.(out_edges));
    FSet.equal (v.(out_indices)) (v'.(out_indices));
    Option.equal v_eq (v.(vvalue)) (v'.(vvalue))
  ] true.


Ltac2 vdata_is_orphan (vd : 'v VData) : bool :=
  List.fold_right Bool.and [FSet.is_empty (vd.(in_edges));
  FSet.is_empty (vd.(out_edges));
  FSet.is_empty (vd.(in_indices));
  FSet.is_empty (vd.(out_indices))] true.



Ltac2 Type 'a EData := {
  s : int list; (* s[ource] *)
  t : int list; (* t[arget] *)
  value : 'a option (* value *)
}.

Ltac2 esource : 'a EData -> int list :=
  fun ed => ed.(s).
Ltac2 etarget : 'a EData -> int list :=
  fun ed => ed.(t).
Ltac2 evalue : 'a EData -> 'a option :=
  fun ed => ed.(value).

Ltac2 mk_edata : int list -> int list -> 'a option -> 'a EData :=
  fun s t value => {
    s := s;
    t := t;
    value := value
}.

Ltac2 ecopy (ed : 'a EData) : 'a EData := {
  s := ed.(s);
  t := ed.(t);
  value := ed.(value)
}.


Ltac2 edata_equal (e_eq : 'e -> 'e -> bool) : 'e EData -> 'e EData -> bool :=
  fun e e' => 
  List.fold_right Bool.and [
    List.equal Int.equal (e.(s)) (e'.(s));
    List.equal Int.equal (e.(t)) (e'.(t));
    Option.equal e_eq (e.(value)) (e'.(value))
  ] true.

Ltac2 Type ('v, 'e) Graph := {
  vdata : (int, 'v VData) FMap.t;
  edata : (int, 'e EData) FMap.t;
  _inputs : int list;
  _outputs : int list;
  _vindex : int;
  _eindex : int;
}.

Ltac2 mk_graph : unit -> ('v, 'e) Graph := fun () => {
  vdata := FMap.empty FSet.Tags.int_tag;
  edata := FMap.empty FSet.Tags.int_tag;
  _inputs := [];
  _outputs := [];
  _vindex := 0;
  _eindex := 0;
}.

Ltac2 mk_graph_from : (int, 'v VData) FMap.t -> (int, 'e EData) FMap.t -> 
  int list -> int list -> int -> int -> ('v, 'e) Graph :=
  fun vdata edata ins outs vidx eidx => {
  vdata := vdata;
  edata := edata;
  _inputs := ins;
  _outputs := outs;
  _vindex := vidx;
  _eindex := eidx;
}.

Ltac2 graph_equal (v_eq : 'v -> 'v -> bool) (e_eq : 'e -> 'e -> bool) : 
  ('v, 'e) Graph -> ('v, 'e) Graph -> bool :=
  fun g g' => List.fold_right Bool.and [
    FMap.equal (vdata_equal v_eq) (g.(vdata)) (g'.(vdata));
    FMap.equal (edata_equal e_eq) (g.(edata)) (g'.(edata));
    List.equal Int.equal (g.(_inputs)) (g'.(_inputs));
    List.equal Int.equal (g.(_outputs)) (g'.(_outputs))
  ] true.

Module GraphPrinting.

Export Message Printf.

Export PrintingExtra.

Import PpExtra.

Ltac2 print_graph (pr_v : 'v -> message) (pr_e : 'e -> message)
  (g : ('v, 'e) Graph) : message :=
  vbox 2 (concats [of_string "Graph with" ; break 1 0 ; 
    vbox 2 (concats [of_string "Vertices:" ; break 1 0 ;
      prlist_with_sep pr_comma
      (fun (v, vd) => 
        hbox (concats [of_int v; of_string " (";
        Option.map_default pr_v (of_string "None") (vvalue vd);
        of_string ")"]))
      (FMap.bindings (g.(vdata))) ]) ; 
    break 1 0;
    vbox 2 (concats [of_string "Edges:" ; break 1 0 ;
      prlist_with_sep pr_comma
      (fun (e, ed) => 
        hbox (concats [of_int e; of_string " (";
        Option.map_default pr_e (of_string "None") (ed.(value));
        of_string ") :"; break 1 2; 
          of_list int (ed.(s)) ++ spc() ++ str "->" ++ spc () ++
          of_list int (ed.(t))]))
      (FMap.bindings (g.(edata)))]) ; 
    break 1 0 ;
    vbox 2 (concats [of_string "Inputs:" ; break 1 0 ;
      hbox (prlist_with_sep pr_comma int (g.(_inputs))) ]) ; 
    break 1 0 ;
    vbox 2 (concats [of_string "Outputs:" ; break 1 0 ;
      hbox (prlist_with_sep pr_comma int (g.(_outputs))) ])]).

Ltac2 print_int_graph g := print_graph of_int of_int g.
Ltac2 print_string_graph g := print_graph of_string of_string g.



Ltac2 pr_edge_to_parse (pr_e : 'e -> message) (e : int) (ed : 'e EData) : message :=
  hov 2 (concats [Option.map_default pr_e (str "") (ed.(value)); spc(); 
    str "("; int e; str ")"; spc(); pr_colon();
    prlist_with_sep pr_comma int (ed.(s)); spc(); str "->"; spc();
    prlist_with_sep pr_comma int (ed.(t))]).

Ltac2 pr_graph_nice (* (pr_v : 'v -> message) *) (pr_e : 'e -> message) 
  (g : ('v, 'e) Graph) : message := 
  let orphans := List.map_filter (fun (v, vd) =>
    if vdata_is_orphan vd then Some v else None) (FMap.bindings (g.(vdata))) in 
  let pr_comma () := concats [of_string ","; break 1 0] in 
  let pr_semicolon () := concats [of_string ";"; break 1 0] in 
  let hov := hovbox in 
  let spc () := break 1 0 in
  let int := of_int in 
  let str := of_string in 
  hov 2 (concats [str "!Graph"; spc(); 
    prlist_with_sep pr_comma int (g.(_inputs)) ; spc(); str "->"; spc();
    prlist_with_sep pr_comma int (g.(_outputs)); spc(); str ":" ; spc(); 

    prlist_with_sep pr_semicolon (fun (e, ed) => pr_edge_to_parse pr_e e ed)
      (FMap.bindings (g.(edata)));

    if List.is_empty orphans then spc() else 
      concats [spc(); str "and"; spc(); prlist_with_sep pr_comma int orphans]]).



Ltac2 pr_vdata (pr_v : 'v -> message) (vd : 'v VData) : message :=
  let pr_comma () := concats [of_string ","; break 1 0] in 
  let hov := hovbox in 
  let spc () := break 1 0 in
  let str := of_string in 
  (* let quote m := concats [str  ] *)
  hov 2 (concats [str "VData with"; spc(); str "{"; 
    str "value = "; (* quote *) 
      (Option.map_default pr_v (str "") (vd.(vvalue))); pr_comma();
    str "in_edges = "; pr_int_set (vd.(in_edges)); pr_comma();
    str "out_edges = "; pr_int_set (vd.(out_edges)); pr_comma();
    str "in_indices = "; pr_int_set (vd.(in_indices)); pr_comma();
    str "out_indices = "; pr_int_set (vd.(out_indices)); str "}"]).

Ltac2 pr_edata (pr_e : 'e -> message) (ed : 'e EData) : message :=
  let pr_comma () := concats [of_string ","; break 1 0] in 
  let hov := hovbox in 
  let spc () := break 1 0 in
  let str := of_string in 
  (* let quote m := concats [str  ] *)
  hov 2 (concats [
  str "EData with"; spc(); str "{"; 
      str "value = "; (Option.map_default pr_e (str "") (ed.(value))); 
      pr_comma();
      str "s = "; pr_int_list (ed.(s)); pr_comma();
      str "t = "; pr_int_list (ed.(t)); str "}"]).

End GraphPrinting.


Ltac2 gcopy (g : ('v, 'e) Graph) : ('v, 'e) Graph := {
  vdata := FMap.mapi (fun _ => vcopy) (g.(vdata));
  edata := FMap.mapi (fun _ => ecopy) (g.(edata));
  _inputs := g.(_inputs);
  _outputs := g.(_outputs);
  _vindex := g.(_vindex);
  _eindex := g.(_eindex);
}.

Ltac2 vdata : ('v, 'e) Graph -> (int, 'v VData) FMap.t :=
  fun g => g.(vdata).

Ltac2 edata : ('v, 'e) Graph -> (int, 'e EData) FMap.t :=
  fun g => g.(edata).

Ltac2 vertices : ('v, 'e) Graph -> int list :=
  fun g => List.map fst (FMap.bindings (g.(vdata))).
  
Ltac2 edges : ('v, 'e) Graph -> int list :=
  fun g => List.map fst (FMap.bindings (g.(edata))).

Ltac2 num_vertices : ('v, 'e) Graph -> int :=
  fun g => FMap.cardinal (vdata g).

Ltac2 num_edges : ('v, 'e) Graph -> int :=
  fun g => FMap.cardinal (edata g).

Ltac2 vertex_data : ('v, 'e) Graph -> int -> 'v VData :=
  fun g i => Option.get (FMap.find_opt i (vdata g)).

Ltac2 edge_data : ('v, 'e) Graph -> int -> 'e EData :=
  fun g i => Option.get (FMap.find_opt i (edata g)).

Ltac2 in_edges : ('v, 'e) Graph -> int -> int FSet.t :=
  fun g i => (vertex_data g i).(in_edges).

Ltac2 out_edges : ('v, 'e) Graph -> int -> int FSet.t :=
  fun g i => (vertex_data g i).(out_edges).

Ltac2 source : ('v, 'e) Graph -> int -> int list :=
  fun g i => (edge_data g i).(s).

Ltac2 target : ('v, 'e) Graph -> int -> int list :=
  fun g i => (edge_data g i).(t).

Ltac2 inputs : ('v, 'e) Graph -> int list :=
  fun g => g.(_inputs).

Ltac2 outputs : ('v, 'e) Graph -> int list :=
  fun g => g.(_outputs).


Ltac2 add_inputs : ('v, 'e) Graph -> int list -> ('v, 'e) Graph :=
  fun g inp =>
    let i1 := List.length (g.(_inputs)) in 
    let i2 := Int.add i1 (List.length inp) in
  let new_ins := List.append (g.(_inputs)) inp in
  let new_vdata := FMap.mapi (
    fun v vd =>
    {vd with in_indices := 
      List.fold_right FSet.add
        (List.filter (fun i => Int.equal (List.nth new_ins i) v) 
          (List.range i1 i2))
        (vd.(in_indices))}) (g.(vdata)) in 
  {g with _inputs := new_ins; vdata := new_vdata}.

Ltac2 add_outputs : ('v, 'e) Graph -> int list -> ('v, 'e) Graph :=
  fun g outp =>
    let i1 := List.length (g.(_outputs)) in 
    let i2 := Int.add i1 (List.length outp) in
  let new_outs := List.append (g.(_outputs)) outp in
  let new_vdata := FMap.mapi (
    fun v vd =>
    {vd with out_indices := 
      List.fold_right FSet.add
        (List.filter (fun i => Int.equal (List.nth new_outs i) v) 
          (List.range i1 i2))
        (vd.(out_indices))}) (g.(vdata)) in 
  {g with _outputs := new_outs; vdata := new_vdata}.

Ltac2 set_inputs : ('v, 'e) Graph -> int list -> ('v, 'e) Graph :=
  fun g inp => 
  let new_ins := inp in 
  let new_vdata := FMap.mapi (fun v vd => 
    {vd with in_indices := FSet.of_list FSet.Tags.int_tag
      (List.map_filter (fun (i, v') => if Int.equal v' v then Some i else None) 
          (List.enumerate new_ins))}
    ) (g.(vdata)) in 
  {g with _inputs := new_ins; vdata := new_vdata}.

Ltac2 set_outputs : ('v, 'e) Graph -> int list -> ('v, 'e) Graph :=
  fun g outp => 
  let new_outs := outp in 
  let new_vdata := FMap.mapi (fun v vd => 
    {vd with out_indices := FSet.of_list FSet.Tags.int_tag
      (List.map_filter (fun (i, v') => if Int.equal v' v then Some i else None) 
          (List.enumerate new_outs))}
    ) (g.(vdata)) in 
  {g with _outputs := new_outs; vdata := new_vdata}.

Ltac2 add_vertex : ('v, 'e) Graph -> 'v option -> int option -> ('v, 'e) Graph * int :=
  fun g value name => 
  let (v, max_index) := 
    Option.map_default (fun name => (name, max name (g.(_vindex))))
      (g.(_vindex), g.(_vindex)) name in 
  ({g with _vindex := Int.add max_index 1 ;
    vdata := FMap.add v (mk_vdata value) (g.(vdata))}, v).

Ltac2 add_edge : ('v, 'e) Graph -> int list -> int list -> 'e option -> 
  int option -> ('v, 'e) Graph * int :=
  fun g s t value name => 
  let (e, max_index) := 
    Option.map_default (fun name => (name, max name (g.(_eindex))))
      (g.(_eindex), g.(_eindex)) name in 
  let new_eindex := Int.add max_index 1 in 
  let new_edata := FMap.add e (mk_edata s t value) (g.(edata)) in 
  let new_vdata := FMap.mapi (fun v vd => 
    {vd with 
      out_edges := (if List.mem Int.equal v s 
        then FSet.add e (vd.(out_edges)) else vd.(out_edges));
      in_edges := if List.mem Int.equal v t
        then FSet.add e (vd.(in_edges)) else vd.(in_edges)}) (g.(vdata)) in 
  ({g with _eindex := new_eindex; vdata := new_vdata; 
    edata := new_edata}, e).


Ltac2 remove_vertex_strict : ('v, 'e) Graph -> int -> ('v, 'e) Graph :=
  fun g i => 
  let v := vertex_data g i in 
  if Bool.or (Int.lt 0 (FSet.cardinal (v.(in_edges))))
    (Int.lt 0 (FSet.cardinal (v.(out_edges)))) then 
    Control.throw 
      (Invalid_argument (Some (Message.of_string
        "Attempting to remove vertex with adjacent edges while strict == True")))
  else 
  if Bool.or 
    (List.exist (Int.equal i) (g.(_inputs)))
    (List.exist (Int.equal i) (g.(_outputs))) then
    Control.throw 
      (Invalid_argument (Some (Message.of_string
        "Attempting to remove boundary vertex while strict == True")))
  else 
  {g with vdata := FMap.remove i (g.(vdata))}.


Ltac2 remove_vertex_nonstrict : ('v, 'e) Graph -> int -> ('v, 'e) Graph :=
  fun g v => 
  let rem_v := List.remove Int.equal v in 
  set_outputs (set_inputs {g with 
    vdata := FMap.remove v (g.(vdata));
    edata := FMap.mapi (fun _e ed => 
      {ed with s := rem_v (ed.(s)); t := rem_v (ed.(t))}) (g.(edata))} 
      (rem_v (inputs g))) (rem_v (outputs g)).

Ltac2 remove_vertex : ('v, 'e) Graph -> int -> bool -> ('v, 'e) Graph :=
  fun g v strict => 
  if strict then remove_vertex_strict g v else
  remove_vertex_nonstrict g v.

Ltac2 remove_edge : ('v, 'e) Graph -> int -> ('v, 'e) Graph :=
  fun g e => 
  {g with 
    vdata := (let rem_e := FSet.remove e in 
      FMap.mapi (fun _v vd => 
        {vd with in_edges := rem_e (vd.(in_edges)); 
          out_edges := rem_e (vd.(out_edges))}) (g.(vdata)));
    edata := FMap.remove e (g.(edata))}.

Ltac2 is_input : ('v, 'e) Graph -> int -> bool :=
  fun g v => Bool.neg (FSet.is_empty ((vertex_data g v).(in_indices))).

Ltac2 is_output : ('v, 'e) Graph -> int -> bool :=
  fun g v => Bool.neg (FSet.is_empty ((vertex_data g v).(out_indices))).

Ltac2 is_boundary : ('v, 'e) Graph -> int -> bool :=
  fun g v => 
  let vd := vertex_data g v in 
  Bool.neg (Bool.and 
    (FSet.is_empty (vd.(in_indices)))
    (FSet.is_empty (vd.(out_indices)))).

Ltac2 successors : ('v, 'e) Graph -> int list -> int FSet.t :=
  fun g vs => 
  let rec go (succ : int FSet.t) (current : int list) :=
    if List.is_empty current then succ else
    let v := List.hd current in 
    let current := List.tl current in 
    let (succ, current) := 
      FSet.fold (fun e (succ, current) => 
        List.fold_right (fun (v1 : int) (succ, current) => 
          if Bool.neg (FSet.mem v1 succ) then 
            (FSet.add v1 succ, List.cons v1 current)
          else (succ, current)) 
          (target g e) (succ, current))
        (out_edges g v) (succ, current) in 
    go succ current in 
  go (FSet.empty FSet.Tags.int_tag) vs.

Ltac2 merge_vertices (g : ('v, 'e) Graph) (v : int) (w : int) : 
  ('v, 'e) Graph :=
  let vd := vertex_data g v in 
  let replace_w_v := (fun x => if Int.equal x w then v else x) in
  let w_in := in_edges g w in 
  let w_out := out_edges g w in 
  let new_edata := FMap.mapi (fun e ed => 
    {ed with 
      s := (if FSet.mem e w_out 
        then List.map replace_w_v (ed.(s)) else (ed.(s)));
      t := (if FSet.mem e w_in 
        then List.map replace_w_v (ed.(t)) else (ed.(t)))
      }) (g.(edata)) in 
  let new_vdata := FMap.add v 
    {vd with 
      in_edges := FSet.union (vd.(in_edges)) w_in;
      out_edges := FSet.union (vd.(out_edges)) w_out} (g.(vdata)) in 
  let g := {g with edata := new_edata; vdata := new_vdata} in 
  let g := set_inputs g (List.map replace_w_v (g.(_inputs))) in 
  let g := set_outputs g (List.map replace_w_v (g.(_outputs))) in
  remove_vertex_nonstrict g w.

(* Ltac2 explode_vertex : ('v, 'e) Graph -> int -> int list * int list * ('v, 'e) Graph :=
  fun g v => 
  let new_vs : int list ref * int list ref := (Ref.ref [], Ref.ref []) in 
  let vd := vertex_data g v in 
  let fresh (j : bool) : int :=
    let v1 := add_vertex g (vvalue vd) (-1)  in 
    Ref.update 
      (if j then fst new_vs else snd new_vs) 
      (fun vs => List.append vs [v1]);
    v1 in 
  
  set_inputs g 
    (List.map (fun v1 => 
      if Int.equal v1 v then fresh false else v1) (g.(_inputs)));

  FSet.fold (fun e () => 
    let ed := edge_data g e in 
    ed.(t) := List.map (fun w => 
      if Int.equal w v then 
        let v1 := fresh false in 
        let v1d := vertex_data g v1 in 
        v1d.(in_edges) := FSet.add e (v1d.(in_edges));
        v1
      else w) (ed.(t)))
    (vd.(in_edges)) ();

  set_outputs g 
    (List.map (fun v1 => 
      if Int.equal v1 v then fresh true else v1) (g.(_outputs)));

  FSet.fold (fun e () => 
    let ed := edge_data g e in 
    ed.(s) := List.map (fun w => 
      if Int.equal w v then 
        let v1 := fresh false in 
        let v1d := vertex_data g v1 in 
        v1d.(out_edges) := FSet.add e (v1d.(out_edges));
        v1
      else w) (ed.(s)))
    (vd.(out_edges)) ();
  
  vd.(in_edges) := FSet.empty FSet.Tags.int_tag;
  vd.(out_edges) := FSet.empty FSet.Tags.int_tag;

  remove_vertex_strict g v;

  (Ref.get (fst new_vs), Ref.get (snd new_vs)). *)

(* Ltac2 insert_id_after (g : ('v, 'e) Graph) (v : int) (reverse : bool) : int := 
  let vd := vertex_data g v in 
  let w := add_vertex g (vvalue vd) (-1) in 
  let wd := vertex_data g w in 
  let replace_v_w := (fun x => if Int.equal x v then w else x) in 
  set_outputs g 
    (List.map replace_v_w (g.(_outputs)));
  
  FSet.fold (fun e () => 
    let ed := edge_data g e in 
    ed.(s) := List.map replace_v_w (ed.(s));
    wd.(out_edges) := FSet.add e (wd.(out_edges))) 
    (vd.(out_edges)) ();
  vd.(out_edges) := FSet.empty FSet.Tags.int_tag;

  let (s, t) := if reverse then ([w], [v]) else ([v], [w]) in 
  let e := add_edge g s t None (-1) in 
  e. *)

Ltac2 tensor (g : ('v, 'e) Graph) (other : ('v, 'e) Graph) :=
  let (g, vmap) (* : (int, int) FMap.t *) := 
    List.fold_right (fun v (g, vmap) => 
      let vd := vertex_data other v in 
      let (g, v') := (add_vertex g (vvalue vd) (Some -1)) in 
      (g, FMap.add v v' vmap)
      ) (vertices other) (g, FMap.empty FSet.Tags.int_tag) in
    
  let g := List.fold_right (fun e g => 
    let ed := edge_data other e in 
    fst (add_edge g (List.map (FMap.lookup vmap) (ed.(s)))
      (List.map (FMap.lookup vmap) (ed.(t))) (ed.(value)) (Some -1))
    ) (edges other) g in 
  
  let g := add_inputs g (List.map (FMap.lookup vmap) (inputs other)) in 
  add_outputs g (List.map (FMap.lookup vmap) (outputs other)).

(* TODO: Copy functions... *)

Import Printf.

(* 
Ltac2 compose (g : ('v, 'e) Graph) (other : ('v, 'e) Graph) :=
  let self_outputs := outputs g in 
  let other_inputs := inputs other in 
  if Bool.neg (Int.equal (List.length self_outputs) (List.length other_inputs)) then
    Control.throw (Invalid_argument (Some
      (Message.of_string "Attempt to compose non-composable graphs"))) else
  
  (* List.fold_right2 (fun output_id input_id () => 
    let output_data := vertex_data g output_id in 
    let input_data := vertex_data other input_id in 
    (* vtype check... *)
    (* size check... *)
    ) self_outputs other_inputs; *)

  let vmap : (int, int) FMap.t := 
    List.fold_right (fun v vmap => 
      let vd := vertex_data other v in 
      FMap.add v (add_vertex g (vvalue vd) -1) vmap
      ) (vertices other) (FMap.empty FSet.Tags.int_tag) in
    
  List.fold_right (fun e () => 
    let ed := edge_data other e in 
    let _ := add_edge g (List.map (FMap.lookup vmap) (ed.(s)))
      (List.map (FMap.lookup vmap) (ed.(t))) (ed.(value)) (-1) in 
    ()
    ) (edges other) ();
  
  let plug1 := outputs g in 
  let plug2 := List.map (FMap.lookup vmap) (inputs other) in 
  (* I believe this check is redundant... *)
  if Bool.neg (Int.equal (List.length plug1) (List.length plug2)) then 
    Control.throw (Invalid_argument (Some
      (fprintf "Attempting to plug a graph with %i outputs into one with %i inputs" 
      (List.length plug1) (List.length plug2)))) else
  
  set_outputs g (List.map (FMap.lookup vmap) (outputs other));

  let _quotient : (int, int) FMap.t := 
    List.fold_right2 (fun p1 p2 quotient => 
      let rec follow_chain (j : int) : int :=
        if FSet.mem j (FMap.domain quotient) then 
          follow_chain (FMap.lookup quotient j)
        else j in 
      let p1 := follow_chain p1 in 
      let p2 := follow_chain p2 in 
      if Bool.neg (Int.equal p1 p2) then 
        (* let data_1 := vertex_data g p1 in 
        let data_2 := vertex_data g p2 in  *)
        (* vtype check, with infer... *)
        (* infer types...*)
        (* sizes check... *)
        (* infer sizes... *)
        merge_vertices g p1 p2;
        FMap.add p2 p1 quotient
      else quotient) plug1 plug2 (FMap.empty FSet.Tags.int_tag) in 
  (). *)

(* Ltac2 domain (g : ('v, 'e) Graph) : unit list :=
  List.map (fun _ => ()) (inputs g).

Ltac2 codomain (g : ('v, 'e) Graph) : unit list :=
  List.map (fun _ => ()) (inputs g).

Ltac2 edge_domain (g : ('v, 'e) Graph) (edge_id : int) : unit list :=
  List.map (fun _ => ()) (source g edge_id).

Ltac2 edge_codomain (g : ('v, 'e) Graph) (edge_id : int) : unit list :=
  List.map (fun _ => ()) (target g edge_id). *)





(* 

Ltac2 gen (value : 'e option) (domain : unit list) (codomain : unit list) : 
  ('v, 'e) Graph :=
  let g := mk_graph () in 
  let inputs := List.map (fun _ => add_vertex g None (-1)) domain in 
  let outputs := List.map (fun _ => add_vertex g None (-1)) codomain in 
  let _ := add_edge g inputs outputs value (-1) in 
  set_inputs g inputs;
  set_outputs g outputs;
  g. *)
  
(* Ltac2 perm (p : int list) (domain : unit list) : ('a, 'b) Graph := 
  let g := mk_graph () in 
  let num_wires := List.length p in 
  if Bool.neg (Int.equal (List.length domain) num_wires) then 
    Control.throw (Invalid_argument (Some 
    (Message.of_string "Domain does not match length of permutation.")))
  else

  let inputs := List.map (fun _ => add_vertex g None (-1)) domain in 
  let outputs := List.map (fun i => List.nth inputs (List.nth p i))
    (List.range 0 num_wires) in 
  set_inputs g inputs;
  set_outputs g outputs;
  g. *)

(* Ltac2 identity : unit -> ('v, 'e) Graph :=
  fun () => 
  let g := mk_graph () in 
  let v := add_vertex g None (-1) in 
  set_inputs g [v];
  set_outputs g [v];
  g. *)

(* TODO: Redistributer *)












Ltac2 mutable debug_match := false.

Ltac2 match_log : message -> unit :=
  fun m => if debug_match then Message.print m else ().


Ltac2 Type ('v, 'e) Match := {
  domain : ('v, 'e) Graph;
  codomain : ('v, 'e) Graph;
  edge_eq : 'e -> 'e -> bool;
  vertex_map : (int, int) FMap.t;
  vertex_image : int FSet.t;
  edge_map : (int, int) FMap.t;
  edge_image : int FSet.t;
}.

Ltac2 match_equal (v_eq : 'v -> 'v -> bool) (e_eq : 'e -> 'e -> bool) : 
  ('v, 'e) Match -> ('v, 'e) Match -> bool :=
  fun m m' => 
  List.fold_right Bool.and [
    graph_equal v_eq e_eq (m.(domain)) (m'.(domain));
    graph_equal v_eq e_eq (m.(codomain)) (m'.(codomain));
    FMap.equal Int.equal (m.(vertex_map)) (m'.(vertex_map));
    FMap.equal Int.equal (m.(edge_map)) (m'.(edge_map));
    FSet.equal (m.(vertex_image)) (m'.(vertex_image));
    FSet.equal (m.(edge_image)) (m'.(edge_image))
  ] true.

Ltac2 mk_match (domain : ('v, 'e) Graph) (codomain : ('v, 'e) Graph) 
  (edge_eq : 'e -> 'e -> bool) : ('v, 'e) Match := {
  domain := domain;
  codomain := codomain;
  edge_eq := edge_eq;
  vertex_map := FMap.empty FSet.Tags.int_tag;
  vertex_image := FSet.empty FSet.Tags.int_tag;
  edge_map := FMap.empty FSet.Tags.int_tag;
  edge_image := FSet.empty FSet.Tags.int_tag
}.

Ltac2 mk_match_from (domain : ('v, 'e) Graph) (codomain : ('v, 'e) Graph) 
  (edge_eq : 'e -> 'e -> bool) vm vi em ei : ('v, 'e) Match := {
  domain := domain;
  codomain := codomain;
  edge_eq := edge_eq;
  vertex_map := vm;
  vertex_image := vi;
  edge_map := em;
  edge_image := ei;
}.

Ltac2 mcopy_deep (m : ('v, 'e) Match) : ('v, 'e) Match := {
  domain := gcopy (m.(domain));
  codomain := gcopy (m.(codomain));
  edge_eq := m.(edge_eq);
  vertex_map := m.(vertex_map);
  vertex_image := m.(vertex_image);
  edge_map := m.(edge_map);
  edge_image := m.(edge_image)
}.

Ltac2 mcopy (m : ('v, 'e) Match) : ('v, 'e) Match := {
  domain := m.(domain);
  codomain := m.(codomain);
  edge_eq := m.(edge_eq);
  vertex_map := m.(vertex_map);
  vertex_image := m.(vertex_image);
  edge_map := m.(edge_map);
  edge_image := m.(edge_image)
}.

Module Printing.
Export GraphPrinting.

Ltac2 print_match (m : ('v, 'e) Match) : message :=
  vbox 2 (concats [of_string "Match with" ; break 1 0;
    of_string "Vertex Map:" ; break 1 2 ; 
      vbox 2 (print_int_map (m.(vertex_map))) ; break 1 0 ;
    of_string "Edge Map:" ; break 1 2;
      vbox 2 (print_int_map (m.(edge_map)))
  ]).

Ltac2 print_match_full (pr_v : 'v -> message) 
  (pr_e : 'e -> message) (m : ('v, 'e) Match) : message :=
  vbox 2 (concats [of_string "Match with" ; break 1 0;
    of_string "Domain: "; break 1 2 ; 
      vbox 2 (print_graph pr_v pr_e (m.(domain))) ; break 1 0;
    of_string "Coomain: "; break 1 2 ; 
      vbox 2 (print_graph pr_v pr_e (m.(codomain))) ; break 1 0;
    of_string "Vertex Map:" ; break 1 2 ; 
      vbox 2 (print_int_map (m.(vertex_map))) ; break 1 0 ;
    of_string "Edge Map:" ; break 1 2;
      vbox 2 (print_int_map (m.(edge_map)))
  ]).

End Printing.

Import PrintingExtra.

Ltac2 try_add_vertex (v_eq : 'v -> 'v -> bool) 
  (m : ('v, 'e) Match) (domain_vertex : int) 
  (codomain_vertex : int) : ('v, 'e) Match option :=
  let _brks (l : message list) : message := 
    Pp.prlist_with_sep (fun () => Message.break 1 2) (fun x => x) l in 
  let mapstr := Message.to_string (fprintf "%i -> %i" domain_vertex codomain_vertex) in 
  match_log (fprintf "Trying to add vertex %s to match:" mapstr);
  
  let b := if FSet.mem domain_vertex (FMap.domain (m.(vertex_map))) then 
    match_log (fprintf "Mapping %s failed; vertex already mapped to %i"
      mapstr (Option.default (-1) (FMap.find_opt domain_vertex (m.(vertex_map)))));
    Int.equal (FMap.lookup (m.(vertex_map)) domain_vertex) codomain_vertex
    else true in 
  if Bool.neg b then None else

  
  (* check types... *)

  (* check sizes... *)

  if Bool.and (is_boundary (m.(codomain)) codomain_vertex) 
    (Bool.neg (is_boundary (m.(domain)) domain_vertex)) then 
    match_log (fprintf "Vertex %s failed: codomain vertex is boundary but domain vertex is not." mapstr);
    None else
  
  let b := if FSet.mem codomain_vertex (m.(vertex_image)) then 
    if Bool.neg (is_boundary (m.(domain)) domain_vertex) then 
      match_log (fprintf "Vertex %s failed: non-injective on interior vertex." mapstr);
      false else
    
    FMap.fold (fun mapped_vertex image_vertex b => 
      if Bool.and (Int.equal image_vertex codomain_vertex)
        (Bool.neg (is_boundary (m.(domain)) mapped_vertex)) then 
        match_log (fprintf "Vertex %s failed: non-injective on interior vertex." mapstr);
        false else b) (m.(vertex_map)) true else true in 
  if Bool.neg b then None else

  let b := if Bool.neg (is_boundary (m.(domain)) domain_vertex) then 
    if Bool.neg 
      (Int.equal (FSet.cardinal (in_edges (m.(domain)) domain_vertex))
        (FSet.cardinal (in_edges (m.(codomain)) codomain_vertex))) then 
      match_log (fprintf "Vertex %s failed: in_edges cannot satisfy gluing conditions." mapstr);
      false else
    if Bool.neg 
      (Int.equal (FSet.cardinal (out_edges (m.(domain)) domain_vertex))
        (FSet.cardinal (out_edges (m.(codomain)) codomain_vertex))) then 
      match_log (fprintf "Vertex %s failed: out_edges cannot satisfy gluing conditions." mapstr);
      false else
    true else true in 
  if Bool.neg b then None else 
  let dvalue := (vertex_data (m.(domain)) domain_vertex).(vvalue) in
  let cdvalue := (vertex_data (m.(codomain)) codomain_vertex).(vvalue) in
  if Bool.neg (Option.equal v_eq dvalue cdvalue) then 
    match_log (fprintf "Vertex %s failed: values did not match; discarding." mapstr); None else 
  (match_log (fprintf "Vertex %s success." mapstr);
  Some {m with 
    vertex_map := FMap.add domain_vertex codomain_vertex (m.(vertex_map));
    vertex_image := FSet.add codomain_vertex (m.(vertex_image))}).


Ltac2 try_add_edge (v_eq : 'v -> 'v -> bool) (m : ('v, 'e) Match) 
  (domain_edge : int) (codomain_edge : int) : ('v, 'e) Match option :=
  let brks (l : message list) : message := 
    Pp.prlist_with_sep (fun () => Message.break 1 2) (fun x => x) l in 
  let mapstr := Message.to_string (fprintf "%i -> %i" domain_edge codomain_edge) in 
  match_log (fprintf "Trying to add edge %s to match:" mapstr);
  
  let domain_value := (edge_data (m.(domain)) domain_edge).(value) in 
  let codomain_value := (edge_data (m.(codomain)) codomain_edge).(value) in 

  if Bool.neg (Option.equal (m.(edge_eq)) domain_value codomain_value) then 
    match_log (fprintf "Edge %s failed: values not equal" mapstr);
    None else
  
  if FSet.mem codomain_edge (m.(edge_image)) then 
    match_log (fprintf "Edge %s failed: the map would become non-injective." mapstr);
    None else

  (* let preimg_edge_domain := edge_domain (m.(domain)) domain_edge in 
  let image_edge_domain := edge_domain (m.(codomain)) codomain_edge in 

  if Bool.neg (List.equal (fun () () => true) 
    preimg_edge_domain image_edge_domain) then 
    match_log (fprintf "edge domain does not match image domain");
    None else 
  
  let preimg_edge_codomain := edge_codomain (m.(domain)) domain_edge in 
  let image_edge_codomain := edge_codomain (m.(codomain)) codomain_edge in 

  if Bool.neg (List.equal (fun () () => true) 
    preimg_edge_codomain image_edge_codomain) then 
    match_log (fprintf "edge codomain does not match image codomain");
    None else  *)

  let domain_sources := source (m.(domain)) domain_edge in 
  let codomain_sources := source (m.(codomain)) codomain_edge in 
  let domain_targets := target (m.(domain)) domain_edge in 
  let codomain_targets := target (m.(codomain)) codomain_edge in 
  let vertices_to_check := List.combine 
    (List.append domain_sources domain_targets) 
    (List.append codomain_sources codomain_targets) in 
  
  let m := List.fold_right (fun (domain_vertex, codomain_vertex) m => 
    Option.bind m (fun m =>
    if FSet.mem domain_vertex (FMap.domain (m.(vertex_map))) then
      if (Bool.neg (Option.equal Int.equal 
        (FMap.find_opt domain_vertex (m.(vertex_map))) 
        (Some codomain_vertex))) then 
        match_log (brks [fprintf "Edge %s failed:" mapstr;
        fprintf "maps vertices %i -> %i" domain_vertex codomain_vertex; 
        fprintf "inconsistent with previously";
        fprintf "mapped vertex (%i -> %i)." domain_vertex 
          (Option.default (-1) (FMap.find_opt domain_vertex (m.(vertex_map))))]);
        None
      else 
        (match_log (fprintf "Vertex map %i -> %i accepted; already included"
          domain_vertex codomain_vertex);
        Some m)
    else
      let m := try_add_vertex v_eq m domain_vertex codomain_vertex in 
      match m with 
      | None => match_log (brks [fprintf "Edge %s failed:" mapstr; 
        fprintf "couldn't add a source or target vertex"]);
          None
      | _ => m
      end))
    vertices_to_check (Some m) in 
  Option.bind m (fun m =>
  (match_log (fprintf "Edge %s success." mapstr);
  Some {m with edge_map := FMap.add domain_edge codomain_edge (m.(edge_map));
    edge_image := FSet.add codomain_edge (m.(edge_image))})).

Ltac2 domain_neighborhood_mapped (m : ('v, 'e) Match) (vertex : int) : bool :=
  Bool.and (* TODO: Is FSet.union faster?*)
    (FSet.subset (in_edges (m.(domain)) vertex) (FMap.domain (m.(edge_map))))
    (FSet.subset (out_edges (m.(domain)) vertex) (FMap.domain (m.(edge_map)))).



(* Ltac2 Eval List.fold_left 
  (fun v (i, b) => Message.print (fprintf "Looking at index %i, value %s" i 
    (if b then "true" else "false"));
  if b then Int.add v 1 else v) 0 (List.enumerate [true; true; false; false]). *)

Ltac2 map_scalars (m : ('v, 'e) Match) : ('v, 'e) Match option :=
  (* TODO: Make a function? *)
  let codomain_scalars := List.map_filter 
    (fun e => let ed := edge_data (m.(codomain)) e in 
      if Bool.and (Int.equal (List.length (ed.(s))) 0) 
          (Int.equal (List.length (ed.(t))) 0) then 
      Some (e, ed.(value)) else None)
    (edges (m.(codomain))) in
  
  let domain_scalars := List.filter 
    (fun e => let ed := edge_data (m.(domain)) e in 
      Bool.and (Int.equal (List.length (ed.(s))) 0) 
        (Int.equal (List.length (ed.(t))) 0)) 
    (edges (m.(domain))) in
  
  let may_m_cs := List.fold_right (fun e m => Option.bind m (fun (m, codomain_scalars) =>  
    match_log (fprintf "Trying to map scalar edge %i" e);
    let ed := edge_data (m.(domain)) e in
    let may_scalar := List.find_opt 
      (fun (_, (_, value)) => Option.equal (m.(edge_eq)) value (ed.(value)))
      (List.enumerate codomain_scalars) in 
    match may_scalar with 
    | Some (i, (codomain_scalar, _value)) => 
      match_log (fprintf "Successfully mapped scalar %i -> %i" 
        e codomain_scalar);
      Some ({m with 
        edge_map := FMap.add e codomain_scalar (m.(edge_map));
        edge_image := FSet.add codomain_scalar (m.(edge_image))}, 
        List.append (List.firstn i codomain_scalars) 
        (List.skipn (Int.add i 1) codomain_scalars))
    | None => 
      match_log (fprintf "Match failed: could not map scalar edge %i." e);
      None
    end)) domain_scalars (Some (m, codomain_scalars)) in 
  Option.map fst may_m_cs.

Ltac2 more (v_eq : 'v -> 'v -> bool) (m : ('v, 'e) Match) : ('v, 'e) Match list :=
  (* TODO: Improve performance (with List.fold_right) to shortcut 
    tries after we find something working *)
  let more_in_edges := List.find_opt (fun l => Bool.neg (List.is_empty l)) 
    (List.map (fun (domain_vertex, codomain_vertex) => 
      if domain_neighborhood_mapped m domain_vertex then [] else
      List.flat_map (fun edge => 
        if FMap.mem edge (m.(edge_map)) then [] else
        List.map_filter (fun codomain_edge => 
          try_add_edge v_eq m edge codomain_edge)
          (FSet.elements (in_edges (m.(codomain)) codomain_vertex))
        )
        (FSet.elements (in_edges (m.(domain)) domain_vertex)))
    (FMap.bindings (m.(vertex_map)))) in 
  match more_in_edges with | Some l => l | None => 
  let more_out_edges := List.find_opt (fun l => Bool.neg (List.is_empty l)) 
    (List.map (fun (domain_vertex, codomain_vertex) => 
      if domain_neighborhood_mapped m domain_vertex then [] else
      List.flat_map (fun edge => 
        if FMap.mem edge (m.(edge_map)) then [] else
        List.map_filter (fun codomain_edge => 
          try_add_edge v_eq m edge codomain_edge)
          (FSet.elements (out_edges (m.(codomain)) codomain_vertex))
        )
        (FSet.elements (out_edges (m.(domain)) domain_vertex)))
    (FMap.bindings (m.(vertex_map)))) in  
  match more_out_edges with | Some l => l | None => 
  let more_verts := List.find_opt (fun l => Bool.neg (List.is_empty l))
    (List.map (fun domain_vertex => 
      if FMap.mem domain_vertex (m.(vertex_map)) then [] else
      List.map_filter (fun codomain_vertex => 
        try_add_vertex v_eq m domain_vertex codomain_vertex)
        (vertices (m.(codomain)))
      ) (vertices (m.(domain)))) in 
  Option.default [] more_verts
  end end.

Ltac2 is_total (m : ('v, 'e) Match) : bool :=
  Bool.and 
    (Int.equal (FMap.cardinal (m.(vertex_map))) (num_vertices (m.(domain))))
    (Int.equal (FMap.cardinal (m.(edge_map))) (num_edges (m.(domain)))).

Ltac2 is_surjective (m : ('v, 'e) Match) : bool :=
  Bool.and 
    (Int.equal (FSet.cardinal (m.(vertex_image))) (num_vertices (m.(codomain))))
    (Int.equal (FSet.cardinal (m.(edge_image))) (num_edges (m.(codomain)))).

Ltac2 is_injective (m : ('v, 'e) Match) : bool :=
  Int.equal (FMap.cardinal (m.(vertex_map))) (FSet.cardinal (m.(vertex_image))).

Ltac2 is_convex (m : ('v, 'e) Match) : bool :=
  if Bool.neg (is_injective m) then false else

  let output_image_successors :=
    successors (m.(codomain)) 
    (List.map_filter
      (fun v => 
      if FSet.mem v (FMap.domain (m.(vertex_map))) then 
        Some (FMap.lookup (m.(vertex_map)) v) else
      None) (outputs (m.(domain)))) in 
  
  for_each (inputs (m.(domain))) (fun v => 
    if FSet.mem v (FMap.domain (m.(vertex_map))) then 
      if FSet.mem (FMap.lookup (m.(vertex_map)) v) output_image_successors then 
        for_return false
      else 
        continue
    else continue
    ) (fun () => true).


Ltac2 Type ('v, 'e) Matches := {
  convex : bool;
  initial_match : ('v, 'e) Match;
  match_stack : ('v, 'e) Match list
}.

Ltac2 mk_matches (edge_eq : 'e -> 'e -> bool)
  (domain : ('v, 'e) Graph) (codomain : ('v, 'e) Graph)
  (initial_match : ('v, 'e) Match option) (convex : bool) : ('v, 'e) Matches := 
  let initial_match := match initial_match with 
    | Some m => m 
    | None => mk_match domain codomain edge_eq
    end in {
  convex := convex;
  initial_match := initial_match;
  match_stack := match map_scalars initial_match with 
    | Some m => [m]
    | None => []
    end
}.

Ltac2 mk_matches_from_stack
  (ms : ('v, 'e) Match list) : ('v, 'e) Matches option :=
  match ms with 
  | [] => None
  | m::ms' => Some {
    convex := false;
    initial_match := m;
    match_stack := (m::ms');
    }
  end.

Ltac2 rec next_match (v_eq : 'v -> 'v -> bool) (ms : ('v, 'e) Matches) : 
  (('v, 'e) Match * ('v, 'e) Matches) option :=
  if List.is_empty (ms.(match_stack)) then None else
  let m := List.hd (ms.(match_stack)) in 
  let ms := {ms with match_stack := List.tl (ms.(match_stack))} in
  if is_total m then 
    match_log (fprintf "got successful match:\n {str(m)}");
    if ms.(convex) then 
      if is_convex m then 
        match_log (fprintf "match is convex, returning");
        Some (m, ms)
      else
        (match_log (fprintf "match is not convex, dropping");
        next_match v_eq ms)
    else
      Some (m, ms)
  else
    next_match v_eq {ms with 
      match_stack := List.append (ms.(match_stack)) (more v_eq m)}.

(* Return the iterable of [Match]es of a [Matches] as a backtracking value *)
Ltac2 rec get_match (v_eq : 'v -> 'v -> bool) (ms : ('v, 'e) Matches) : ('v, 'e) Match :=
  match next_match v_eq ms with 
  | None => Control.zero (Invalid_argument (Some (fprintf "No more matches")))
  | Some (m, ms') => Control.plus (fun () => m) (fun _ => get_match v_eq ms')
  end.

(* Return the iterable of [Match]es of a [Matches] as a list *)
Ltac2 rec get_matches (v_eq : 'v -> 'v -> bool) 
  (ms : ('v, 'e) Matches) : ('v, 'e) Match list :=
  match next_match v_eq ms with 
  | None => []
  | Some (m, ms') => List.cons m (get_matches v_eq ms')
  end.

Ltac2 match_graph (v_eq : 'v -> 'v -> bool ) (edge_eq : 'e -> 'e -> bool) 
  (domain : ('v, 'e) Graph) (codomain : ('v, 'e) Graph) : ('v, 'e) Match list :=
  get_matches v_eq (mk_matches edge_eq domain codomain None false).

Ltac2 find_iso (v_eq : 'v -> 'v -> bool) (edge_eq : 'e -> 'e -> bool) 
  (domain : ('v, 'e) Graph) (codomain : ('v, 'e) Graph) : ('v, 'e) Match option :=
  if Bool.neg (Bool.and 
    (Int.equal (num_vertices domain) (num_vertices codomain))
    (Int.equal (num_edges domain) (num_edges codomain))) then None else
  List.find_opt is_surjective (match_graph v_eq edge_eq domain codomain).


