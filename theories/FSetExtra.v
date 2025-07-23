Require Ltac2.Ltac2.
Import Ltac2.Init.


Module FSet.
Export FSet.
Ltac2 fold : ('a -> 'b -> 'b) -> 'a FSet.t -> 'b -> 'b :=
  fun f s b => List.fold_right f (FSet.elements s) b.

Ltac2 of_list : 'a Tags.tag -> 'a list -> 'a t :=
  fun tag l => List.fold_left (fun s a => FSet.add a s) (FSet.empty tag) l.

Ltac2 filter : ('a -> bool) -> 'a FSet.t -> 'a FSet.t :=
  fun f s => 
  FSet.fold (fun a acc_s => if f a then acc_s else FSet.remove a acc_s)
    s s.

End FSet.

Module FMap.
Export FMap.

Ltac2 find_default (def : 'b) (key : 'a) : ('a, 'b) FMap.t -> 'b :=
  fun m => Option.default def (FMap.find_opt key m).

Ltac2 update (f : 'b -> 'b) (key : 'a) (m : ('a, 'b) FMap.t) : ('a, 'b) FMap.t :=
  match FMap.find_opt key m with 
  | Some v => FMap.add key (f v) m
  | None => m
  end.

Ltac2 update_opt (f : 'b option -> 'b) (key : 'a) 
  (m : ('a, 'b) FMap.t) : ('a, 'b) FMap.t :=
  FMap.add key (f (FMap.find_opt key m)) m.

Ltac2 set : 'a -> 'b option -> ('a, 'b) FMap.t -> ('a, 'b) FMap.t :=
  fun a may_b m => 
  match may_b with 
  | Some b => FMap.add a b m
  | None => FMap.remove a m
  end.

Ltac2 modify (f : 'b option -> 'b option) (key : 'a) 
  (m : ('a, 'b) FMap.t) : ('a, 'b) FMap.t :=
  FMap.set key (f (FMap.find_opt key m)) m.

Ltac2 lookup : ('a, 'b) FMap.t -> 'a -> 'b :=
  fun m a =>
  Option.get (FMap.find_opt a m).

Ltac2 filter : ('a -> 'b -> bool) -> ('a, 'b) FMap.t -> ('a, 'b) FMap.t :=
  fun f m => 
  FMap.fold (fun a b m_acc => if f a b then m_acc else FMap.remove a m) m m.

(* Ltac2 mapi_filter : ('a -> 'b -> 'c option) -> ('a, 'b) FMap.t 
  -> ('a, 'c) FMap.t := *)

Ltac2 fold2 : ('a -> 'b option -> 'c option -> 'acc -> 'acc) -> 
  ('a, 'b) FMap.t -> ('a, 'c) FMap.t -> 'acc -> 'acc :=
  fun f m m' init =>
  let dom := FSet.union (FMap.domain m) (FMap.domain m') in 
  FSet.fold (fun a acc => f a (FMap.find_opt a m) (FMap.find_opt a m') acc)
    dom init.

Ltac2 equal (v_eq : 'v -> 'v -> bool) : 
  ('k, 'v) FMap.t -> ('k, 'v) FMap.t -> bool :=
  fun m m' => 
  Bool.and (Int.equal (FMap.cardinal m) (FMap.cardinal m')) (
    FMap.fold2 (fun _k may_v may_v' b => 
      Bool.and b 
      (match may_v, may_v' with 
      | Some v, Some v' => v_eq v v'
      | None, None => true
      | _, _ => false
      end)) m m' true).

End FMap.


Module FSet2.

Import FSet.Tags.

Ltac2 Type ('a, 'b) t := 'b tag * ('a, 'b FSet.t) FMap.t.

Ltac2 empty : 'a tag -> 'b tag -> ('a, 'b) t :=
  fun ta tb => (tb, FMap.empty ta).

Ltac2 is_empty (m : ('a, 'b) t) : bool :=
  FMap.fold (fun _ s_b => Bool.and (FSet.is_empty s_b)) (snd m) true.

Ltac2 mem : 'a -> 'b -> ('a, 'b) t -> bool :=
  fun a b m => 
  Option.map_default (FSet.mem b) false (FMap.find_opt a (snd m)).

Ltac2 add : 'a -> 'b -> ('a, 'b) t -> ('a, 'b) t :=
  fun a b m =>
  (fst m, FMap.update_opt (fun may_m => match may_m with 
    | Some s_b => FSet.add b s_b
    | None => FSet.add b (FSet.empty (fst m))
    end) a (snd m)).

Ltac2 remove : 'a -> 'b -> ('a, 'b) t -> ('a, 'b) t :=
  fun a b (t, m) => (t, FMap.update (FSet.remove b) a m).

Ltac2 union : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t :=
  fun (tb, m) (_, m') => 
  (tb, FMap.fold (fun a s_b m_acc => 
    FMap.update_opt (Option.map_default (FSet.union s_b) s_b) a m_acc) m m').

Ltac2 inter : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t :=
  fun (tb, m) (_, m') => 
  (tb, FMap.fold (fun a s_b m_acc => 
    FMap.modify (fun may_b => Option.bind may_b 
      (fun s_b' => let new_s_b := FSet.inter s_b s_b' in 
        if FSet.is_empty new_s_b then None else Some new_s_b)) a m_acc) m m').

Ltac2 diff : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t :=
  fun (tb, m) (_, m') => 
  (tb, FMap.fold (fun a s_b m_acc => 
    FMap.update (FSet.diff s_b) a m_acc) m m').

Ltac2 remove_empty : ('a, 'b) t -> ('a, 'b) t :=
  fun (t, m) => 
  (t, FMap.fold (fun a s_b m_acc => 
    if FSet.is_empty s_b then FMap.remove a m_acc else m_acc) m m).

Ltac2 equal : ('a, 'b) t -> ('a, 'b) t -> bool :=
  fun (_, m) (_, m') => 
  FMap.fold2 (fun _ may_s_b may_s_b' => Bool.and (
    match (may_s_b, may_s_b') with (* they must either: *)
    | Some s_b, Some s_b' => FSet.equal s_b s_b' (* Have the same value *)
    | Some s_b, None => FSet.is_empty s_b (* Or differ only by empty sets *)
    | None, Some s_b' => FSet.is_empty s_b'
    | None, None => true (* (we shouldn't hit this case but just in case) *) 
    end)
  ) m m' true.

Ltac2 fix_fst : 'a -> ('a, 'b) t -> 'b FSet.t :=
  fun a (t, m) => 
  match FMap.find_opt a m with 
  | Some s_b => s_b
  | None => FSet.empty t
  end.

Ltac2 fix_snd : 'b -> ('a, 'b) t -> 'a FSet.t :=
  fun b (_, m) => 
  FSet.filter (FSet.mem b) (FMap.domain m).

Ltac2 subset : ('a, 'b) t -> ('a, 'b) t -> bool :=
  fun (_, m) m' => 
  FMap.fold (fun a s_b => Bool.and (FSet.subset s_b (fix_fst a m'))) m true.

Ltac2 cardinal : ('a, 'b) t -> int :=
  fun (_, m) => 
  FMap.fold (fun _ s_b => Int.add (FSet.cardinal s_b)) m 0.

Ltac2 elements : ('a, 'b) t -> ('a * 'b) list :=
  fun (_, m) => 
  FMap.fold (fun a s_b => 
  List.append (List.map (fun b => (a, b)) (FSet.elements s_b))) m [].



Ltac2 fold : ('a -> 'b -> 'acc -> 'acc) -> ('a, 'b) t -> 'acc -> 'acc :=
  fun f s init => List.fold_right (fun (a, b) => f a b) (elements s) init.

Ltac2 of_list : 'a tag -> 'b tag -> ('a * 'b) list -> ('a, 'b) t :=
  fun ta tb l => 
    List.fold_left (fun s (a, b) => FSet2.add a b s) (FSet2.empty ta tb) l.

Ltac2 filter : ('a -> 'b -> bool) -> ('a, 'b) t -> ('a, 'b) t :=
  fun f (t, m) => 
  (t, FMap.mapi (fun a => FSet.filter (f a)) m).

End FSet2.


Module FMap2.

Import FSet.Tags.

Ltac2 Type ('a, 'b, 'c) t := 'b tag * ('a, ('b, 'c) FMap.t) FMap.t.

Ltac2 empty : 'a tag -> 'b tag -> ('a, 'b, 'c) t :=
  fun ta tb => (tb, FMap.empty ta).

Ltac2 is_empty (m : ('a, 'b, 'c) t) : bool :=
  FMap.fold (fun _ m_bc => Bool.and (FMap.is_empty m_bc)) (snd m) true.

Ltac2 mem : 'a -> 'b -> ('a, 'b, 'c) t -> bool :=
  fun a b m => 
  Option.map_default (FMap.mem b) false (FMap.find_opt a (snd m)).

Ltac2 add : 'a -> 'b -> 'c -> ('a, 'b, 'c) t -> ('a, 'b, 'c) t :=
  fun a b c m =>
  (fst m, FMap.update_opt (fun may_m => match may_m with 
    | Some m_bc => FMap.add b c m_bc
    | None => FMap.add b c (FMap.empty (fst m))
    end) a (snd m)).

Ltac2 remove_fst : 'a -> ('a, 'b, 'c) t -> ('a, 'b, 'c) t :=
  fun a (t, m) => (t, FMap.remove a m).

Ltac2 remove : 'a -> 'b -> ('a, 'b, 'c) t -> ('a, 'b, 'c) t :=
  fun a b (t, m) => 
  (t, FMap.modify (fun may_b => Option.bind may_b
    (fun m_bc => let m_bc' := FMap.remove b m_bc in 
    if FMap.is_empty m_bc' then None else Some m_bc')) a m).

Ltac2 find_opt : 'a -> 'b -> ('a, 'b, 'c) t -> 'c option :=
  fun a b m => 
  Option.bind (FMap.find_opt a (snd m)) (FMap.find_opt b).

Ltac2 fix_fst : 'a -> ('a, 'b, 'c) t -> ('b, 'c) FMap.t :=
  fun a m => 
  Option.default (FMap.empty (fst m)) (FMap.find_opt a (snd m)).

Ltac2 fix_snd : 'b -> ('a, 'b, 'c) t -> ('a, 'c) FMap.t :=
  fun b (_, m) => 
  FMap.mapi (fun _ m_bc => FMap.lookup m_bc b) 
    (FMap.filter (fun _ => FMap.mem b) m).

Ltac2 mapi : ('a -> 'b -> 'c -> 'd) -> ('a, 'b, 'c) t -> ('a, 'b, 'd) t :=
  fun f m => (fst m, FMap.mapi (fun a => FMap.mapi (f a)) (snd m)).

Ltac2 fold : ('a -> 'b -> 'c -> 'acc -> 'acc) -> ('a, 'b, 'c) t -> 'acc -> 'acc :=
  fun f m => FMap.fold (fun a => FMap.fold (f a)) (snd m).

Ltac2 cardinal : ('a, 'b, 'c) t -> int :=
  fun (_, m) => FMap.fold 
    (fun _ m_bc acc => Int.add (FMap.cardinal m_bc) acc) m 0.

Ltac2 bindings : ('a, 'b, 'c) t -> ('a * 'b * 'c) list :=
  fun m => List.flat_map (fun (a, m_bc) => 
    List.map (fun (b, c) => (a, b, c)) (FMap.bindings m_bc))
    (FMap.bindings (snd m)).

Ltac2 domain : ('a, 'b, 'c) t -> ('a, 'b) FSet2.t :=
  fun (t, m) => (t, FMap.mapi (fun _ b => FMap.domain b) m).




Ltac2 find_default (def : 'c) (a : 'a) (b : 'b) : ('a, 'b, 'c) t -> 'c :=
  fun m => Option.default def (find_opt a b m).

Ltac2 update (f : 'c -> 'c) (a : 'a) (b : 'b) (m : ('a, 'b, 'c) t) : ('a, 'b, 'c) t :=
  match find_opt a b m with 
  | Some v => add a b (f v) m
  | None => m
  end.

Ltac2 update_opt (f : 'c option -> 'c) (a : 'a) (b : 'b)
  (m : ('a, 'b, 'c) t) : ('a, 'b, 'c) t :=
  add a b (f (find_opt a b m)) m.

Ltac2 set : 'a -> 'b -> 'c option -> ('a, 'b, 'c) t -> ('a, 'b, 'c) t :=
  fun a b may_c m => 
  match may_c with 
  | Some c => add a b c m
  | None => remove a b m
  end.

Ltac2 modify (f : 'c option -> 'c option) (a : 'a) (b : 'b)
  (m : ('a, 'b, 'c) t) : ('a, 'b, 'c) t :=
  set a b (f (find_opt a b m)) m.

Ltac2 lookup : ('a, 'b, 'c) t -> 'a -> 'b -> 'c :=
  fun (_, m) a b =>
  FMap.lookup (FMap.lookup m a) b.

Ltac2 filter : ('a -> 'b -> 'c -> bool) -> 
  ('a, 'b, 'c) t -> ('a, 'b, 'c) t :=
  fun f (t, m) => 
  (t, FMap.mapi (fun a => FMap.filter (f a)) m).

Ltac2 fold2 : ('a -> 'b -> 'c option -> 'd option -> 'acc -> 'acc) -> 
  ('a, 'b, 'c) t -> ('a, 'b, 'd) t -> 'acc -> 'acc :=
  fun f (_, m) (_, m') init =>
  let dom := FSet.union (FMap.domain m) (FMap.domain m') in 
  FSet.fold (fun a acc => 
    match (FMap.find_opt a m, FMap.find_opt a m') with 
    | (Some m_bc, Some m_bd) => 
      FMap.fold2 (f a) m_bc m_bd acc
    | (Some m_bc, None) => 
      FMap.fold (fun b c => f a b (Some c) None) m_bc acc
    | (None, Some m_bd) => 
      FMap.fold (fun b d => f a b None (Some d)) m_bd acc
    | (None, None) => acc (* We should never reach this case, but just in case *)
    end)
    dom init.

End FMap2.

Module FSet3.

Import FSet.Tags.

Ltac2 Type ('a, 'b, 'c) t := 'c tag * ('a, 'b, 'c FSet.t) FMap2.t.

Ltac2 empty : 'a tag -> 'b tag -> 'c tag -> ('a, 'b, 'c) t :=
  fun ta tb tc => (tc, FMap2.empty ta tb).

Ltac2 is_empty (m : ('a, 'b, 'c) t) : bool :=
  FMap2.fold (fun _ _ s_b => Bool.and (FSet.is_empty s_b)) (snd m) true.

Ltac2 mem : 'a -> 'b -> 'c -> ('a, 'b, 'c) t -> bool :=
  fun a b c m => 
  Option.map_default (FSet.mem c) false (FMap2.find_opt a b (snd m)).

Ltac2 add : 'a -> 'b -> 'c -> ('a, 'b, 'c) t -> ('a, 'b, 'c) t :=
  fun a b c m =>
  (fst m, FMap2.update_opt (fun may_m => match may_m with 
    | Some s_c => FSet.add c s_c
    | None => FSet.add c (FSet.empty (fst m))
    end) a b (snd m)).

Ltac2 remove : 'a -> 'b -> 'c -> ('a, 'b, 'c) t -> ('a, 'b, 'c) t :=
  fun a b c (t, m) => (t, FMap2.update (FSet.remove c) a b m).

Ltac2 union : ('a, 'b, 'c) t -> ('a, 'b, 'c) t -> ('a, 'b, 'c) t :=
  fun (tb, m) (_, m') => 
  (tb, FMap2.fold (fun a b s_c m_acc => 
    FMap2.update_opt (Option.map_default (FSet.union s_c) s_c) a b m_acc) m m').

Ltac2 inter : ('a, 'b, 'c) t -> ('a, 'b, 'c) t -> ('a, 'b, 'c) t :=
  fun (tb, m) (_, m') => 
  (tb, FMap2.fold (fun a b s_c m_acc => 
    FMap2.modify (fun may_c => Option.bind may_c 
      (fun s_c' => let new_s_c := FSet.inter s_c s_c' in 
        if FSet.is_empty new_s_c then None else Some new_s_c)) a b m_acc) m m').

Ltac2 diff : ('a, 'b, 'c) t -> ('a, 'b, 'c) t -> ('a, 'b, 'c) t :=
  fun (tb, m) (_, m') => 
  (tb, FMap2.fold (fun a b s_c m_acc => 
    FMap2.update (FSet.diff s_c) a b m_acc) m m').

Ltac2 remove_empty : ('a, 'b, 'c) t -> ('a, 'b, 'c) t :=
  fun (t, m) => 
  (t, FMap2.fold (fun a b s_c m_acc => 
    if FSet.is_empty s_c then FMap2.remove a b m_acc else m_acc) m m).

Ltac2 equal : ('a, 'b, 'c) t -> ('a, 'b, 'c) t -> bool :=
  fun (_, m) (_, m') => 
  FMap2.fold2 (fun _ _ may_s_b may_s_b' => Bool.and (
    match (may_s_b, may_s_b') with (* they must either: *)
    | Some s_b, Some s_b' => FSet.equal s_b s_b' (* Have the same value *)
    | Some s_b, None => FSet.is_empty s_b (* Or differ only by empty sets *)
    | None, Some s_b' => FSet.is_empty s_b'
    | None, None => true (* (we shouldn't hit this case but just in case) *) 
    end)
  ) m m' true.

Ltac2 fix_fst : 'a -> ('a, 'b, 'c) t -> ('b, 'c) FSet2.t :=
  fun a (t, m) => 
  (t, FMap2.fix_fst a m).

Ltac2 fix_snd : 'b -> ('a, 'b, 'c) t -> ('a, 'c) FSet2.t :=
  fun a (t, m) => 
  (t, FMap2.fix_snd a m).

Ltac2 fix_thd : 'c -> ('a, 'b, 'c) t -> ('a, 'b) FSet2.t :=
  fun c m => FMap2.domain (FMap2.filter (fun _ _ => FSet.mem c) (snd m)).

Ltac2 subset : ('a, 'b, 'c) t -> ('a, 'b, 'c) t -> bool :=
  fun (_, m) m' => 
  FMap2.fold (fun a b s_c => Bool.and 
    (FSet.subset s_c (FSet2.fix_fst b (fix_fst a m')))) m true.

Ltac2 cardinal : ('a, 'b, 'c) t -> int :=
  fun (_, m) => 
  FMap2.fold (fun _ _ s_c => Int.add (FSet.cardinal s_c)) m 0.

Ltac2 elements : ('a, 'b, 'c) t -> ('a * 'b * 'c) list :=
  fun (_, m) => 
  FMap2.fold (fun a b s_c => 
  List.append (List.map (fun c => (a, b, c)) (FSet.elements s_c))) m [].



Ltac2 fold : ('a -> 'b -> 'c -> 'acc -> 'acc) -> ('a, 'b, 'c) t -> 'acc -> 'acc :=
  fun f s init => List.fold_right (fun (a, b, c) => f a b c) (elements s) init.

Ltac2 of_list : 'a tag -> 'b tag -> 'c tag -> 
  ('a * 'b * 'c) list -> ('a, 'b, 'c) t :=
  fun ta tb tc l => 
    List.fold_left (fun s (a, b, c) => add a b c s) (empty ta tb tc) l.

Ltac2 filter : ('a -> 'b -> 'c -> bool) -> ('a, 'b, 'c) t -> ('a, 'b, 'c) t :=
  fun f (t, m) => 
  (t, FMap2.mapi (fun a b => FSet.filter (f a b)) m).

End FSet3.


Module FMap3.

Import FSet.Tags.

Ltac2 Type ('a, 'b, 'c, 'd) t := 'c tag * ('a, 'b, ('c, 'd) FMap.t) FMap2.t.

Ltac2 empty : 'a tag -> 'b tag -> 'c tag -> ('a, 'b, 'c, 'd) t :=
  fun ta tb tc => (tc, FMap2.empty ta tb).

Ltac2 is_empty (m : ('a, 'b, 'c, 'd) t) : bool :=
  FMap2.fold (fun _ _ m_cd => Bool.and (FMap.is_empty m_cd)) (snd m) true.

Ltac2 mem : 'a -> 'b -> 'c -> ('a, 'b, 'c, 'd) t -> bool :=
  fun a b c m => 
  Option.map_default (FMap.mem c) false (FMap2.find_opt a b (snd m)).

Ltac2 add : 'a -> 'b -> 'c -> 'd -> ('a, 'b, 'c, 'd) t -> ('a, 'b, 'c, 'd) t :=
  fun a b c d m =>
  (fst m, FMap2.update_opt (fun may_m => match may_m with 
    | Some m_cd => FMap.add c d m_cd
    | None => FMap.add c d (FMap.empty (fst m))
    end) a b (snd m)).

Ltac2 remove_fst : 'a -> ('a, 'b, 'c, 'd) t -> ('a, 'b, 'c, 'd) t :=
  fun a (t, m) => (t, FMap2.remove_fst a m).

Ltac2 remove_fst_snd : 'a -> 'b -> ('a, 'b, 'c, 'd) t -> ('a, 'b, 'c, 'd) t :=
  fun a b (t, m) => (t, FMap2.remove a b m).

Ltac2 remove : 'a -> 'b -> 'c -> ('a, 'b, 'c, 'd) t -> ('a, 'b, 'c, 'd) t :=
  fun a b c (t, m) => 
  (t, FMap2.modify (fun may_c => Option.bind may_c
    (fun m_cd => let m_cd' := FMap.remove c m_cd in 
    if FMap.is_empty m_cd' then None else Some m_cd')) a b m).

Ltac2 find_opt : 'a -> 'b -> 'c -> ('a, 'b, 'c, 'd) t -> 'd option :=
  fun a b c m => 
  Option.bind (FMap2.find_opt a b (snd m)) (FMap.find_opt c).

Ltac2 fix_fst : 'a -> ('a, 'b, 'c, 'd) t -> ('b, 'c, 'd) FMap2.t :=
  fun a m => 
  (fst m, FMap2.fix_fst a (snd m)).

Ltac2 fix_snd : 'b -> ('a, 'b, 'c, 'd) t -> ('a, 'c, 'd) FMap2.t :=
  fun b m => 
  (fst m, FMap2.fix_snd b (snd m)).

Ltac2 fix_thd : 'c -> ('a, 'b, 'c, 'd) t -> ('a, 'b, 'd) FMap2.t :=
  fun c (_, m) => 
  FMap2.mapi (fun _ _ m_cd => FMap.lookup m_cd c) 
    (FMap2.filter (fun _ _ => FMap.mem c) m).

Ltac2 mapi : ('a -> 'b -> 'c -> 'd -> 'e) -> 
  ('a, 'b, 'c, 'd) t -> ('a, 'b, 'c, 'e) t :=
  fun f m => (fst m, FMap2.mapi (fun a b => FMap.mapi (f a b)) (snd m)).

Ltac2 fold : ('a -> 'b -> 'c -> 'd -> 'acc -> 'acc) -> 
  ('a, 'b, 'c, 'd) t -> 'acc -> 'acc :=
  fun f m => FMap2.fold (fun a b => FMap.fold (f a b)) (snd m).

Ltac2 cardinal : ('a, 'b, 'c, 'd) t -> int :=
  fun (_, m) => FMap2.fold 
    (fun _ _ m_cd acc => Int.add (FMap.cardinal m_cd) acc) m 0.

Ltac2 bindings : ('a, 'b, 'c, 'd) t -> ('a * 'b * 'c * 'd) list :=
  fun m => List.flat_map (fun (a, b, m_cd) => 
    List.map (fun (c, d) => (a, b, c, d)) (FMap.bindings m_cd))
    (FMap2.bindings (snd m)).

Ltac2 domain : ('a, 'b, 'c, 'd) t -> ('a, 'b, 'c) FSet3.t :=
  fun (t, m) => (t, FMap2.mapi (fun _ _ m_cd => FMap.domain m_cd) m).




Ltac2 find_default (def : 'd) (a : 'a) (b : 'b) (c : 'c) : 
  ('a, 'b, 'c, 'd) t -> 'd :=
  fun m => Option.default def (find_opt a b c m).

Ltac2 update (f : 'd -> 'd) (a : 'a) (b : 'b) (c : 'c) 
  (m : ('a, 'b, 'c, 'd) t) : ('a, 'b, 'c, 'd) t :=
  match find_opt a b c m with 
  | Some v => add a b c (f v) m
  | None => m
  end.

Ltac2 update_opt (f : 'd option -> 'd) (a : 'a) (b : 'b) (c : 'c)
  (m : ('a, 'b, 'c, 'd) t) : ('a, 'b, 'c, 'd) t :=
  add a b c (f (find_opt a b c m)) m.

Ltac2 set : 'a -> 'b -> 'c -> 'd option -> 
  ('a, 'b, 'c, 'd) t -> ('a, 'b, 'c, 'd) t :=
  fun a b c may_d m => 
  match may_d with 
  | Some d => add a b c d m
  | None => remove a b c m
  end.

Ltac2 modify (f : 'd option -> 'd option) (a : 'a) (b : 'b) (c : 'c)
  (m : ('a, 'b, 'c, 'd) t) : ('a, 'b, 'c, 'd) t :=
  set a b c (f (find_opt a b c m)) m.

Ltac2 lookup : ('a, 'b, 'c, 'd) t -> 'a -> 'b -> 'c -> 'd :=
  fun (_, m) a b c =>
  FMap.lookup (FMap2.lookup m a b) c.

Ltac2 filter : ('a -> 'b -> 'c -> 'd -> bool) -> 
  ('a, 'b, 'c, 'd) t -> ('a, 'b, 'c, 'd) t :=
  fun f (t, m) => 
  (t, FMap2.mapi (fun a b => FMap.filter (f a b)) m).

Ltac2 domain_fst : ('a, 'b, 'c, 'd) t -> 'a FSet.t :=
  fun m => FMap.domain (snd (FMap2.domain (snd m))).

Ltac2 fold2 : ('a -> 'b -> 'c -> 'd option -> 'e option -> 'acc -> 'acc) -> 
  ('a, 'b, 'c, 'd) t -> ('a, 'b, 'c, 'e) t -> 'acc -> 'acc :=
  fun f m m' init =>
  let dom := FSet.union (domain_fst m) (domain_fst m') in 
  FSet.fold (fun a acc => 
    FMap2.fold2 (f a) (fix_fst a m) (fix_fst a m') acc)
    dom init.

End FMap3.

