Require PrintingExtra.
Require Import Ltac2.Init.
Require ListExtra.
Require Ltac2.Ltac2.

Set Default Proof Mode "Classic".

Ltac2 max (x : int) (y : int) : int :=
  if Int.lt x y then y else x.

Require Import FSetExtra.


Import ListExtra.ListForEach.

Ltac2 Type VType := string option.

Ltac2 Type 'a VData := {
  (* vtype : VType ; (* vtype *) *)
  mutable in_edges : int FSet.t; (* in_edges *)
  mutable out_edges : int FSet.t; (* out_edges *)
  mutable in_indices : int FSet.t; (* in_indices *)
  mutable out_indices : int FSet.t; (* out_indices *)
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

(* Import Printf. 
Ltac2 Eval let v := mk_vdata (Some ()) in 
  printf "Size of v.in_edges = %i" (FSet.cardinal (v.(in_edges)));
  let v' := v in 
  let v'' := vcopy v in
  v.(in_edges) := FSet.add 1 (v.(in_edges));
  printf "Size of v.in_edges = %i" (FSet.cardinal (v.(in_edges)));
  printf "Size of v'.in_edges = %i" (FSet.cardinal (v'.(in_edges)));
  printf "Size of v''.in_edges = %i" (FSet.cardinal (v''.(in_edges))).
 *)


Ltac2 Type 'a EData := {
  mutable s : int list; (* s[ource] *)
  mutable t : int list; (* t[arget] *)
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
  mutable vdata : (int, 'v VData) FMap.t;
  mutable edata : (int, 'e EData) FMap.t;
  mutable _inputs : int list;
  mutable _outputs : int list;
  mutable _vindex : int;
  mutable _eindex : int;
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


Ltac2 add_inputs : ('v, 'e) Graph -> int list -> unit :=
  fun g inp =>
    let i1 := List.length (g.(_inputs)) in 
    let i2 := Int.add i1 (List.length inp) in
  g.(_inputs) := List.append (g.(_inputs)) inp;
  for_each (List.range i1 i2) 
    (fun i => 
    let v := List.nth (g.(_inputs)) i in 
    let vd := vertex_data g v in 
    vd.(in_indices) := FSet.add i (vd.(in_indices));
    continue) (fun () => ()).

Ltac2 add_outputs : ('v, 'e) Graph -> int list -> unit :=
  fun g outp =>
    let i1 := List.length (g.(_outputs)) in 
    let i2 := Int.add i1 (List.length outp) in
  g.(_outputs) := List.append (g.(_outputs)) outp;
  for_each (List.range i1 i2) 
    (fun i => 
    let v := List.nth (g.(_outputs)) i in 
    let vd := vertex_data g v in 
    vd.(out_indices) := FSet.add i (vd.(out_indices));
    continue) (fun () => ()).

Ltac2 set_inputs : ('v, 'e) Graph -> int list -> unit :=
  fun g inp => 
  g.(_inputs) := inp;
  FMap.fold (fun _ vd () => 
      vd.(in_indices) := FSet.empty FSet.Tags.int_tag) 
    (g.(vdata)) ();
  List.fold_right (fun (i, v) () => 
      let vd := vertex_data g v in 
      vd.(in_indices) := FSet.add i (vd.(in_indices))) 
    (List.enumerate (g.(_inputs))) ().

Ltac2 set_outputs : ('v, 'e) Graph -> int list -> unit :=
  fun g outp => 
  g.(_outputs) := outp;
  FMap.fold (fun _ vd () => 
      vd.(out_indices) := FSet.empty FSet.Tags.int_tag) 
    (g.(vdata)) ();
  List.fold_right (fun (i, v) () => 
      let vd := vertex_data g v in 
      vd.(out_indices) := FSet.add i (vd.(out_indices))) 
    (List.enumerate (g.(_outputs))) ().

Ltac2 add_vertex : ('v, 'e) Graph -> 'v option -> int option -> int :=
  fun g value name => 
  let (v, max_index) := 
    Option.map_default (fun name => (name, max name (g.(_vindex))))
      (g.(_vindex), g.(_vindex)) name in 
  g.(_vindex) := Int.add max_index 1;
  g.(vdata) := FMap.add v (mk_vdata value) (g.(vdata));
  v.

Ltac2 add_edge : ('v, 'e) Graph -> int list -> int list -> 'e option -> 
  int option -> int :=
  fun g s t value name => 
  let (e, max_index) := 
    Option.map_default (fun name => (name, max name (g.(_eindex))))
      (g.(_eindex), g.(_eindex)) name in 
  g.(_eindex) := Int.add max_index 1;
  g.(edata) := FMap.add e (mk_edata s t value) (g.(edata));

  List.fold_right (fun i () => 
    let v := vertex_data g i in  
    v.(out_edges) := FSet.add e (v.(out_edges))) s ();
  List.fold_right (fun i () => 
    let v := vertex_data g i in  
    v.(in_edges) := FSet.add e (v.(in_edges))) t ();
    
  (* This _might_ be faster? Depends on the relationship between the sizes of
     s, t, and the number of vertices of the graph: 
  FMap.fold 
    (fun i vd () => 
      if List.exist (Int.equal i) s then 
        vd.(out_edges) := FSet.add e (vd.(out_edges))
        else ();
      if List.exist (Int.equal i) t then 
        vd.(in_edges) := FSet.add e (vd.(in_edges))
        else ()
        ) (g.(vdata)) (); *)
  e.

Import Printf.

Ltac2 remove_vertex_strict : ('v, 'e) Graph -> int -> unit :=
  fun g i => 
  let v := vertex_data g i in 
  if Bool.or (Int.lt 0 (FSet.cardinal (v.(in_edges))))
    (Int.lt 0 (FSet.cardinal (v.(out_edges)))) then 
    Control.throw 
      (Invalid_argument (Some (fprintf "%s"
        "Attempting to remove vertex with adjacent edges while strict == True")))
  else 
  if Bool.or 
    (List.exist (Int.equal i) (g.(_inputs)))
    (List.exist (Int.equal i) (g.(_outputs))) then
    Control.throw 
      (Invalid_argument (Some (fprintf "%s"
        "Attempting to remove boundary vertex while strict == True")))
  else 
  g.(vdata) := FMap.remove i (g.(vdata)).


Ltac2 remove_vertex_nonstrict : ('v, 'e) Graph -> int -> unit :=
  fun g v => 
  let vd := vertex_data g v in 
  FSet.fold (fun e () => let ed := edge_data g e in 
      ed.(t) := List.remove Int.equal v (ed.(t)))
    (vd.(in_edges)) ();
  FSet.fold (fun e () => let ed := edge_data g e in 
      ed.(s) := List.remove Int.equal v (ed.(s)))
    (vd.(out_edges)) ();
  
  set_inputs g (List.remove Int.equal v (inputs g));
  set_outputs g (List.remove Int.equal v (outputs g));

  g.(vdata) := FMap.remove v (g.(vdata)).

Ltac2 remove_vertex : ('v, 'e) Graph -> int -> bool -> unit :=
  fun g v strict => 
  if strict then remove_vertex_strict g v else
  remove_vertex_nonstrict g v.

Ltac2 remove_edge : ('v, 'e) Graph -> int -> unit :=
  fun g e => 
  let ed := edge_data g e in 
  List.fold_right (fun v () => 
    let vd := vertex_data g v in 
    vd.(out_edges) := FSet.remove e (vd.(out_edges))) (ed.(s)) ();
  List.fold_right (fun v () => 
    let vd := vertex_data g v in 
    vd.(in_edges) := FSet.remove e (vd.(in_edges))) (ed.(t)) ();
  g.(edata) := FMap.remove e (g.(edata)).

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

Ltac2 merge_vertices (g : ('v, 'e) Graph) (v : int) (w : int) : unit :=
  let vd := vertex_data g v in 
  let replace_w_v := (fun x => if Int.equal x w then v else x) in 
  FSet.fold (fun e () => 
    let ed := edge_data g e in 
    ed.(t) := List.map replace_w_v (ed.(t));
    vd.(in_edges) := FSet.add e (vd.(in_edges))
  ) (in_edges g w) ();
  FSet.fold (fun e () => 
    let ed := edge_data g e in 
    ed.(s) := List.map replace_w_v (ed.(s));
    vd.(out_edges) := FSet.add e (vd.(out_edges))
  ) (out_edges g w) ();
  set_inputs g (List.map replace_w_v (g.(_inputs)));
  set_outputs g (List.map replace_w_v (g.(_outputs)));
  remove_vertex_nonstrict g w.

Ltac2 explode_vertex : ('v, 'e) Graph -> int -> int list * int list :=
  fun g v => 
  let new_vs : int list ref * int list ref := (Ref.ref [], Ref.ref []) in 
  let vd := vertex_data g v in 
  let fresh (j : bool) : int :=
    let v1 := add_vertex g (vvalue vd) None  in 
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

  (Ref.get (fst new_vs), Ref.get (snd new_vs)).

Ltac2 insert_id_after (g : ('v, 'e) Graph) (v : int) (reverse : bool) : int := 
  let vd := vertex_data g v in 
  let w := add_vertex g (vvalue vd) None in 
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
  let e := add_edge g s t None None in 
  e.

Ltac2 tensor (g : ('v, 'e) Graph) (other : ('v, 'e) Graph) :=
  let vmap : (int, int) FMap.t := 
    List.fold_right (fun v vmap => 
      let vd := vertex_data other v in 
      FMap.add v (add_vertex g (vvalue vd) None) vmap
      ) (vertices other) (FMap.empty FSet.Tags.int_tag) in
    
  List.fold_right (fun e () => 
    let ed := edge_data other e in 
    let _ := add_edge g (List.map (FMap.lookup vmap) (ed.(s)))
      (List.map (FMap.lookup vmap) (ed.(t))) (ed.(value)) None in 
    ()
    ) (edges other) ();
  
  add_inputs g (List.map (FMap.lookup vmap) (inputs other));
  add_outputs g (List.map (FMap.lookup vmap) (outputs other)).

(* TODO: Copy functions... *)

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
      FMap.add v (add_vertex g (vvalue vd) None) vmap
      ) (vertices other) (FMap.empty FSet.Tags.int_tag) in
    
  List.fold_right (fun e () => 
    let ed := edge_data other e in 
    let _ := add_edge g (List.map (FMap.lookup vmap) (ed.(s)))
      (List.map (FMap.lookup vmap) (ed.(t))) (ed.(value)) None in 
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
  ().

Ltac2 domain (g : ('v, 'e) Graph) : unit list :=
  List.map (fun _ => ()) (inputs g).

Ltac2 codomain (g : ('v, 'e) Graph) : unit list :=
  List.map (fun _ => ()) (inputs g).

Ltac2 edge_domain (g : ('v, 'e) Graph) (edge_id : int) : unit list :=
  List.map (fun _ => ()) (source g edge_id).

Ltac2 edge_codomain (g : ('v, 'e) Graph) (edge_id : int) : unit list :=
  List.map (fun _ => ()) (target g edge_id).



(* Ltac2 domain : ... *)
(* Ltac2 codomain : ... *)
(* Ltac2 edge_domain : ... *)
(* Ltac2 edge_codomain : ... *)





Ltac2 gen (value : 'e option) (domain : unit list) (codomain : unit list) : 
  ('v, 'e) Graph :=
  let g := mk_graph () in 
  let inputs := List.map (fun _ => add_vertex g None None) domain in 
  let outputs := List.map (fun _ => add_vertex g None None) codomain in 
  let _ := add_edge g inputs outputs value None in 
  set_inputs g inputs;
  set_outputs g outputs;
  g.
  
Ltac2 perm (p : int list) (domain : unit list) : ('a, 'b) Graph := 
  let g := mk_graph () in 
  let num_wires := List.length p in 
  if Bool.neg (Int.equal (List.length domain) num_wires) then 
    Control.throw (Invalid_argument (Some 
    (Message.of_string "Domain does not match length of permutation.")))
  else

  let inputs := List.map (fun _ => add_vertex g None None) domain in 
  let outputs := List.map (fun i => List.nth inputs (List.nth p i))
    (List.range 0 num_wires) in 
  set_inputs g inputs;
  set_outputs g outputs;
  g.

Ltac2 identity : unit -> ('v, 'e) Graph :=
  fun () => 
  let g := mk_graph () in 
  let v := add_vertex g None None in 
  set_inputs g [v];
  set_outputs g [v];
  g.

(* TODO: Redistributer *)












Ltac2 mutable debug_match := false.

Ltac2 match_log : message -> unit :=
  fun m => if debug_match then Message.print m else ().


Ltac2 Type ('v, 'e) Match := {
  domain : ('v, 'e) Graph;
  codomain : ('v, 'e) Graph;
  edge_eq : 'e -> 'e -> bool;
  mutable vertex_map : (int, int) FMap.t;
  mutable vertex_image : int FSet.t;
  mutable edge_map : (int, int) FMap.t;
  mutable edge_image : int FSet.t;
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

Ltac2 try_add_vertex (v_eq : 'v -> 'v -> bool)
  (m : ('v, 'e) Match) (domain_vertex : int) 
  (codomain_vertex : int) : bool :=
  let _brks (l : message list) : message := 
    PrintingExtra.Pp.prlist_with_sep (fun () => Message.break 1 2) (fun x => x) l in 
  let mapstr := Message.to_string (fprintf "%i -> %i" domain_vertex codomain_vertex) in 
  match_log (fprintf "Trying to add vertex %i -> %i to match:" 
    domain_vertex codomain_vertex);

  let dvalue := (vertex_data (m.(domain)) domain_vertex).(vvalue) in
  let cdvalue := (vertex_data (m.(codomain)) codomain_vertex).(vvalue) in
  if Bool.neg (Option.equal v_eq dvalue cdvalue) then 
    match_log (fprintf "Vertex %s failed: values did not match; discarding." mapstr); false else 
  
  if FSet.mem domain_vertex (FMap.domain (m.(vertex_map))) then 
    match_log (fprintf "Vertex already mapped to %i"
      (FMap.lookup (m.(vertex_map)) domain_vertex));
    Option.equal Int.equal (FMap.find_opt domain_vertex (m.(vertex_map))) (Some codomain_vertex) else
  
  (* check types... *)

  (* check sizes... *)

  if Bool.and (is_boundary (m.(codomain)) codomain_vertex) 
    (Bool.neg (is_boundary (m.(domain)) domain_vertex)) then 
    match_log (fprintf "Vertex failed: codomain vertex is boundary but domain vertex is not.");
    false else
  
  let b := if FSet.mem codomain_vertex (m.(vertex_image)) then 
    if Bool.neg (is_boundary (m.(domain)) domain_vertex) then 
      match_log (fprintf "Vertex failed: non-injective on interior vertex.");
      false else
    
    FMap.fold (fun mapped_vertex image_vertex b => 
      if Bool.and (Int.equal image_vertex codomain_vertex)
        (Bool.neg (is_boundary (m.(domain)) mapped_vertex)) then 
        match_log (fprintf "Vertex failed: non-injective on interior vertex.");
        false else b) (m.(vertex_map)) true else true in 
  if Bool.neg b then false else

  let b := if Bool.neg (is_boundary (m.(domain)) domain_vertex) then 
    if Bool.neg 
      (Int.equal (FSet.cardinal (in_edges (m.(domain)) domain_vertex))
        (FSet.cardinal (in_edges (m.(codomain)) codomain_vertex))) then 
      match_log (fprintf "Vertex failed: in_edges cannot satisfy gluing conditions.");
      false else
    if Bool.neg 
      (Int.equal (FSet.cardinal (out_edges (m.(domain)) domain_vertex))
        (FSet.cardinal (out_edges (m.(codomain)) codomain_vertex))) then 
      match_log (fprintf "Vertex failed: out_edges cannot satisfy gluing conditions.");
      false else
    true else true in 
  if Bool.neg b then false else 

  (m.(vertex_map) := FMap.add domain_vertex codomain_vertex (m.(vertex_map));
  m.(vertex_image) := FSet.add codomain_vertex (m.(vertex_image));

  match_log (fprintf "Vertex success.");
  true).

Ltac2 try_add_edge (v_eq : 'v -> 'v -> bool) (m : ('v, 'e) Match) 
  (domain_edge : int) (codomain_edge : int) : bool :=
  match_log (fprintf "Trying to add edge %i -> %i to match:" 
    domain_edge codomain_edge);
  
  let domain_value := (edge_data (m.(domain)) domain_edge).(value) in 
  let codomain_value := (edge_data (m.(codomain)) codomain_edge).(value) in 

  if Bool.neg (Option.equal (m.(edge_eq)) domain_value codomain_value) then 
    match_log (fprintf "Edge failed: values not equal");
    false else
  
  if FSet.mem codomain_edge (m.(edge_image)) then 
    match_log (fprintf "Edge failed: the map would become non-injective.");
    false else

  let preimg_edge_domain := edge_domain (m.(domain)) domain_edge in 
  let image_edge_domain := edge_domain (m.(codomain)) codomain_edge in 

  if Bool.neg (List.equal (fun () () => true) 
    preimg_edge_domain image_edge_domain) then 
    match_log (fprintf "edge domain does not match image domain");
    false else 
  
  let preimg_edge_codomain := edge_codomain (m.(domain)) domain_edge in 
  let image_edge_codomain := edge_codomain (m.(codomain)) codomain_edge in 

  if Bool.neg (List.equal (fun () () => true) 
    preimg_edge_codomain image_edge_codomain) then 
    match_log (fprintf "edge codomain does not match image codomain");
    false else 

  let domain_sources := source (m.(domain)) domain_edge in 
  let codomain_sources := source (m.(codomain)) codomain_edge in 
  let domain_targets := target (m.(domain)) domain_edge in 
  let codomain_targets := target (m.(codomain)) codomain_edge in 
  let vertices_to_check := List.combine 
    (List.append domain_sources domain_targets) 
    (List.append codomain_sources codomain_targets) in 
  
  let b := List.fold_right (fun (domain_vertex, codomain_vertex) b => 
    if (FSet.mem domain_vertex (FMap.domain (m.(vertex_map)))) then
      if (Bool.neg (Option.equal Int.equal (FMap.find_opt domain_vertex (m.(vertex_map))) 
          (Some codomain_vertex))) then 
        match_log (fprintf "Edge failed: inconsistent with previously mapped vertex.");
        false
      else 
        b
    else 
      if Bool.neg (try_add_vertex v_eq m domain_vertex codomain_vertex) then 
        match_log (fprintf "Edge failed: couldn't add a source or target vertex");
        false
      else b)
    vertices_to_check true in 
  if Bool.neg b then false else 

  (m.(edge_map) := FMap.add domain_edge codomain_edge (m.(edge_map));
  m.(edge_image) := FSet.add codomain_edge (m.(edge_image));

  match_log (fprintf "Edge success.");
  true).

Ltac2 domain_neighborhood_mapped (m : ('v, 'e) Match) (vertex : int) : bool :=
  Bool.and (* TODO: Is FSet.union faster?*)
    (FSet.subset (in_edges (m.(domain)) vertex) (FMap.domain (m.(edge_map))))
    (FSet.subset (out_edges (m.(domain)) vertex) (FMap.domain (m.(edge_map)))).



(* Ltac2 Eval List.fold_left 
  (fun v (i, b) => Message.print (fprintf "Looking at index %i, value %s" i 
    (if b then "true" else "false"));
  if b then Int.add v 1 else v) 0 (List.enumerate [true; true; false; false]). *)

Ltac2 map_scalars (m : ('v, 'e) Match) : bool :=
  (* TODO: Make a function? *)
  let codomain_scalars := Ref.ref (List.map_filter 
    (fun e => let ed := edge_data (m.(codomain)) e in 
      if Bool.and (Int.equal (List.length (ed.(s))) 0) 
          (Int.equal (List.length (ed.(t))) 0) then 
      Some (e, ed.(value)) else None)
    (edges (m.(codomain)))) in
  
  let domain_scalars := List.filter 
    (fun e => let ed := edge_data (m.(domain)) e in 
      Bool.and (Int.equal (List.length (ed.(s))) 0) 
        (Int.equal (List.length (ed.(t))) 0)) 
    (edges (m.(domain))) in
  
  for_each domain_scalars (fun e => 
    match_log (fprintf "Trying to map scalar edge %i" e);
    let ed := edge_data (m.(domain)) e in
    let found_match := 
      for_each (List.enumerate (Ref.get codomain_scalars))
        (fun (i, (codomain_scalar, value)) => 
          if Option.equal (m.(edge_eq)) value (ed.(value)) then 
            m.(edge_map) := FMap.add e codomain_scalar (m.(edge_map));
            m.(edge_image) := FSet.add codomain_scalar (m.(edge_image));
            Ref.update codomain_scalars (fun cs => 
              List.append (List.firstn i cs) (List.skipn (Int.add i 1) cs));
            match_log (fprintf "Successfully mapped scalar %i -> %i" 
              e codomain_scalar);
            for_return true
          else
            continue) (fun () => false) in 
    if Bool.neg found_match then 
      match_log (fprintf "Match failed: could not map scalar edge %i." e);
      for_return false
    else
      continue
    ) (fun () => true).

Ltac2 more v_eq (m : ('v, 'e) Match) : ('v, 'e) Match list :=
  let extended_matches : ('v, 'e) Match list ref := Ref.ref [] in 
  for_each (FSet.elements (FMap.domain (m.(vertex_map)))) (* TODO: Test performance of this versus FMap.elements *)
    (fun domain_vertex => 
    if domain_neighborhood_mapped m domain_vertex then 
      continue else
    let codomain_vertex := (* TODO: See above; performance would definitely be better with elements *)
      FMap.lookup (m.(vertex_map)) domain_vertex in 
    for_each (FSet.elements (in_edges (m.(domain)) domain_vertex)) 
      (fun edge =>
      if FSet.mem edge (FMap.domain (m.(edge_map))) then 
        continue else
        
      (for_each (FSet.elements (in_edges (m.(codomain)) codomain_vertex))
        (fun codomain_edge => 
        let potential_new_match := mcopy m in 
        if try_add_edge v_eq potential_new_match edge codomain_edge then 
          Ref.update extended_matches 
            (fun em => List.cons potential_new_match em);
          continue
        else continue) (fun () => ());
      for_return (for_return (Ref.get extended_matches)))) (* return out of two nested for loops *)
    (fun () => (* no in_edges matched; try out_edges *)
      for_each (FSet.elements (in_edges (m.(domain)) domain_vertex)) 
      (fun edge =>
      if FSet.mem edge (FMap.domain (m.(edge_map))) then 
        continue else
        
      (for_each (FSet.elements (in_edges (m.(codomain)) codomain_vertex))
        (fun codomain_edge => 
        let potential_new_match := mcopy m in 
        if try_add_edge v_eq potential_new_match edge codomain_edge then 
          Ref.update extended_matches 
            (fun em => List.cons potential_new_match em);
          continue
        else continue) (fun () => ());
      for_return (for_return (Ref.get extended_matches)))) (* return out of two nested for loops *)
      (fun () => (* no out_edges matched either; we've got nothing *) continue)
    )) (fun () => (* no edge extensions; try non-domain vertices *)
    for_each (vertices (m.(domain)))
    (fun domain_vertex => 
      if FSet.mem domain_vertex (FMap.domain (m.(vertex_map))) then 
        continue else (
      
      for_each (vertices (m.(codomain))) 
      (fun codomain_vertex => 
        let potential_new_match := mcopy m in 
        if try_add_vertex v_eq potential_new_match domain_vertex codomain_vertex then 
          Ref.update extended_matches 
            (fun em => List.cons potential_new_match em);
          continue
        else continue) (fun () => ());
      for_return (Ref.get extended_matches))
    ) (fun () => (* no vertex extensions either; we've got nothing *) [])
  ).

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
  mutable match_stack : ('v, 'e) Match list
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
  match_stack := if map_scalars initial_match then 
    [initial_match] else []
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

Ltac2 rec next_match v_eq (ms : ('v, 'e) Matches) : 
  ('v, 'e) Match option :=
  if List.is_empty (ms.(match_stack)) then None else
  let m := List.hd (ms.(match_stack)) in 
  ms.(match_stack) := List.tl (ms.(match_stack));
  if is_total m then 
    match_log (fprintf "got successful match:\n {str(m)}");
    if ms.(convex) then 
      if is_convex m then 
        match_log (fprintf "match is convex, returning");
        Some m
      else
        (match_log (fprintf "match is not convex, dropping");
        next_match v_eq ms)
    else
      Some m
  else
    (ms.(match_stack) := List.append (ms.(match_stack)) (more v_eq m);
    next_match v_eq ms).

(* Return the iterable of [Match]es of a [Matches] as a backtracking value *)
Ltac2 rec get_match v_eq (ms : ('v, 'e) Matches) : ('v, 'e) Match :=
  match next_match v_eq ms with 
  | None => Control.zero (Invalid_argument (Some (fprintf "No more matches")))
  | Some m => Control.plus (fun () => m) (fun _ => get_match v_eq ms)
  end.

(* Return the iterable of [Match]es of a [Matches] as a list *)
Ltac2 rec get_matches
  v_eq (ms : ('v, 'e) Matches) : ('v, 'e) Match list :=
  match next_match v_eq ms with 
  | None => []
  | Some m => List.cons m (get_matches v_eq ms)
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



