(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import psem compiler_util constant_prop_proof.
Require Export psem stack_alloc.
Require Import byteset.
Require Import Psatz.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.
Local Open Scope Z_scope.

Import Region.

(* --------------------------------------------------------------------------- *)

Section Section.

Variables (pmap:pos_map) (stk_size glob_size:Z).
Variables (rsp rip: ptr).

Variable (Slots : Sv.t).
Variable (Addr : slot -> ptr).
Variable (Writable : slot -> bool).
Variable (Align : slot -> wsize).

(* Any pointer in a slot is valid. *)
Definition slot_valid m := forall s p, Sv.In s Slots ->
  between (Addr s) (size_slot s) p U8 -> valid_pointer m p U8.

(* NOTE: disjoint_zrange already contains no_overflow conditions *)
(* Slots are disjoint from the source memory [ms]. *)
Definition disjoint_source ms :=
  forall s p ws, Sv.In s Slots -> valid_pointer ms p ws ->
  disjoint_zrange (Addr s) (size_slot s) p (wsize_size ws).

(* Addresses of slots can be manipulated without risking overflows. *)
Hypothesis addr_no_overflow : forall s, Sv.In s Slots ->
  no_overflow (Addr s) (size_slot s).

(* Two distinct slots, with at least one of them writable, are disjoint. *)
Hypothesis disjoint_writable : forall s1 s2,
  Sv.In s1 Slots -> Sv.In s2 Slots -> s1 <> s2 ->
  Writable s1 ->
  disjoint_zrange (Addr s1) (size_slot s1) (Addr s2) (size_slot s2).

(* The address [Addr s] of a slot s is aligned w.r.t. [Align s]. *)
Hypothesis slot_align :
  forall s, Sv.In s Slots -> is_align (Addr s) (Align s).

(* All pointers valid in memory [m0] are valid in memory [m].
   It is supposed to be applied with [m0] the initial target memory
   and [m] the current target memory.
*)
Definition valid_incl m0 m :=
  forall p ws, valid_pointer m0 p ws -> valid_pointer m p ws.

(* ms: source memory
   m0: initial target memory
   m: current target memory

   ms:
                                              --------------------
                                              |    mem source    |
                                              --------------------

   m0:
   ------------- --------------- ------------ --------------------
   |   stack   | | other stack | |   glob   | |    mem source    |
   ------------- --------------- ------------ --------------------

                                  ||
                                  || execution
                                  \/

   m:
   ------------- --------------- ------------ --------------------
   |   stack   | | other stack | |   glob   | |    mem source    |
   ------------- --------------- ------------ --------------------

*)

(* The memory zones that are not in a writable slot remain unchanged. *)
Definition disjoint_writable_is_constant ms m0 m :=
  forall p ws, valid_pointer m0 p ws -> ~ valid_pointer ms p ws ->
  (forall s, Sv.In s Slots -> Writable s -> disjoint_zrange (Addr s) (size_slot s) p (wsize_size ws)) ->
  read_mem m0 p ws = read_mem m p ws.

(* The stack and the global space are disjoint (if both non-trivial) *)
(* TODO: Is this really needed? *)
Hypothesis disj_rsp_rip :
  0 < stk_size -> 0 < glob_size ->
  wunsigned rsp + stk_size <= wunsigned rip \/ wunsigned rip + glob_size <= wunsigned rsp.

(* TODO: move ? *)
Lemma valid_align m p ws :
  valid_pointer m p ws →
  is_align p ws.
Proof. by case/Memory.valid_pointerP. Qed.

Hint Resolve is_align_no_overflow valid_align.

Record wf_global g ofs ws := {
  wfg_slot : Sv.In g Slots;
  wfg_writable : ~ Writable g;
  wfg_align : Align g = ws;
  wfg_offset : Addr g = (rip + wrepr Uptr ofs)%R
}.

Definition wbase_ptr sc :=
  if sc == Sglob then rip else rsp.

Record wf_direct (x : var) (s : slot) ofs ws z sc := {
  wfd_slot : Sv.In s Slots;
  wfd_size : size_slot x <= z.(z_len);
  wfd_zone : 0 <= z.(z_ofs) /\ z.(z_ofs) + z.(z_len) <= size_slot s;
  wfd_writable : Writable s = (sc != Sglob);
  wfd_align : Align s = ws;
  wfd_offset : Addr s = (wbase_ptr sc + wrepr Uptr ofs)%R
}.

(* TODO : move elsewhere *)
(* but not clear where
   Uptr is defined in memory_model, no stype there
   stype is defined in type, no Uptr there
*)
Notation sptr := (sword Uptr) (only parsing).

Record wf_regptr x xr := {
  wfr_type : is_sarr (vtype x);
  wfr_rtype : vtype xr = sptr;
  wfr_not_vrip : xr <> pmap.(vrip);
  wfr_not_vrsp : xr <> pmap.(vrsp);
  wfr_new : Sv.In xr pmap.(vnew);
  wfr_distinct : forall y yr,
    get_local pmap y = Some (Pregptr yr) -> x <> y -> xr <> yr
}.

Record wf_stkptr (x : var) (s : slot) ofs ws z (xf : var) := {
  wfs_slot : Sv.In s Slots;
  wfs_type : is_sarr (vtype x);
  wfs_size : wsize_size Uptr <= z.(z_len);
  wfs_zone : 0 <= z.(z_ofs) /\ z.(z_ofs) + z.(z_len) <= size_slot s;
  wfs_writable : Writable s;
  wfs_align : Align s = ws;
  wfs_offset : Addr s = (rsp + wrepr Uptr ofs)%R;
  wfs_ftype : vtype xf = sptr;
  wfs_new : Sv.In xf pmap.(vnew);
  wfs_distinct : forall y s' ofs' ws' z' yf,
    get_local pmap y = Some (Pstkptr s' ofs' ws' z' yf) -> x <> y -> xf <> yf
}.

(* ou faire un match *)
Definition wf_local x pk :=
  match pk with
  | Pdirect s ofs ws z sc => wf_direct x s ofs ws z sc
  | Pregptr xr => wf_regptr x xr
  | Pstkptr s ofs ws z xf => wf_stkptr x s ofs ws z xf
  end.

Class wf_pmap := {
  wt_rip     : vtype pmap.(vrip) = sword Uptr;
  wt_rsp     : vtype pmap.(vrsp) = sword Uptr;
  rip_in_new : Sv.In pmap.(vrip) pmap.(vnew);
  rsp_in_new : Sv.In pmap.(vrsp) pmap.(vnew);
  wf_globals : forall g ofs ws, Mvar.get pmap.(globals) g = Some (ofs, ws) -> wf_global g ofs ws;
  wf_locals  : forall x pk, Mvar.get pmap.(locals) x = Some pk -> wf_local x pk
}.

(* Declare Instance wf_pmapI : wf_pmap. *)

(* Well-formedness of a [mp]. *)
Record wf_region (r : region) := {
  wfr_slot     : Sv.In r.(r_slot) Slots;
  wfr_writable : Writable r.(r_slot) = r.(r_writable);
  wfr_align    : Align r.(r_slot) = r.(r_align);
}.

Record wf_zone (z : zone) (ty : stype) (sl : slot) := {
  wfz_len : size_of ty <= z.(z_len);
    (* the zone is big enough to store a value of type [ty] *)
  wfz_ofs : 0 <= z.(z_ofs) /\ z.(z_ofs) + z.(z_len) <= size_slot sl
    (* the zone is a small enough to be in slot [sl] *)
}.

(* Well-formedness of a [sub_region]. *)
Record wf_sub_region (sr : sub_region) ty := {
  wfsr_region :> wf_region sr.(sr_region);
  wfsr_zone   :> wf_zone sr.(sr_zone) ty sr.(sr_region).(r_slot)
}.

(* TODO: Tout exprimer à partier de check_gvalid ? *)
Definition wf_var_region (rmap : region_map) :=
  forall x sr,
    Mvar.get rmap.(var_region) x = Some sr ->
    wf_sub_region sr x.(vtype).

(* TODO :
  - invariant : si une variable n'est pas un tableau, alors sa région a exactement sa taille (peut-être pas nécessaire)
  - gros invariant restant : parler des bytes valides !
  - invariant : si je suis dans local_map, je ne suis ni int ni bool
  - dire des trucs sur la map region_var
*)

(*Definition valid_mp mp ty := 
  exists x, 
    subtype ty (vtype x) /\
    if mp.(mp_s) == MSglob then get_global pmap x = ok mp.(mp_ofs)
    else get_local pmap x = Some (Pstack mp.(mp_ofs)).
*)

(* Registers hold the same value in [vm1] and [vm2] *)
Definition eq_vm (vm1 vm2:vmap) := 
  forall (x:var), Mvar.get pmap.(locals) x = None -> get_var vm1 x = get_var vm2 x.

(*
Definition wptr ms := 
  if ms == MSglob then rip else rsp.

Definition wptr_size sc :=
  if sc == Sglob then glob_size else stk_size.

Definition disjoint_ptr m :=
  forall w sz ms,
    valid_pointer m w sz ->
    ~ ( wunsigned (wbase_ptr ms) < wunsigned w + wsize_size sz /\ wunsigned w < wunsigned (wbase_ptr ms) + wptr_size ms).
*)
Definition sub_region_addr sr :=
  (Addr sr.(sr_region).(r_slot) + wrepr _ sr.(sr_zone).(z_ofs))%R.

(* TODO : could we merge [eq_mp_word] and [eq_mp_array] ? *)
Definition eq_sub_region_word (m2:mem) sr bytes sz v := 
  exists w:word sz,
    v = Vword w /\
    (ByteSet.mem bytes {| imin := sr.(sr_zone).(z_ofs); imax := sr.(sr_zone).(z_ofs) + wsize_size sz |} ->
      read_mem m2 (sub_region_addr sr) sz = ok w).

Definition eq_sub_region_array (m2:mem) sr bytes s v := 
  exists (a:WArray.array s),
   v = Varr a /\
   forall off, (0 <= off < Zpos s)%Z ->
     ByteSet.memi bytes (sr.(sr_zone).(z_ofs) + off) ->
     forall v, WArray.get AAscale U8 a off = ok v ->
     read_mem m2 (sub_region_addr sr + wrepr _ off) U8 = ok v.

Definition eq_sub_region_val ty (m2:mem) sr bytes v := 
  match ty with
  | sword ws => eq_sub_region_word m2 sr bytes ws v
  | sarr  s  => eq_sub_region_array m2 sr bytes s v 
  | _        => True
  end.

Variable (P: uprog) (ev: extra_val_t (progT := progUnit)).
Notation gd := (p_globs P).

(* FIXME : est-ce qu'on teste la bonne zone dans le cas skptr ?
   Doit-on tester une largeur de z_len ou plus précisément Uptr ?
*)
Definition valid_pk rmap (s2:estate) sr pk :=
  match pk with
  | Pdirect s ofs ws z sc =>
    sr = sub_region_direct s ws sc z
  | Pstkptr s ofs ws z f =>
    let srf := sub_region_stkptr s ws z in
    check_stack_ptr rmap s ws z f = ok tt ->
    read_mem s2.(emem) (sub_region_addr srf) Uptr = ok (sub_region_addr sr)
    (* si f est dans la rmap et que ses bytes sont sets, 
    exists sr', Mvar.get f rmap.(var_region) = Some sr' /\
    read_mem s2.(emem) (sub_region_addr sr') Uptr = ok (sub_region_addr sr) *)
    (* read_mem s2.(emem) (mp_addr {| mp_s := MSstack; mp_ofs := ofs |}) Uptr = ok (mp_addr mp) *)
  | Pregptr p =>
    get_var s2.(evm) p = ok (Vword (sub_region_addr sr))
  end.

(* TODO: could we have this in stack_alloc.v ?
   -> could be used in check_valid/set_arr_word...
   This could mean useless checks for globals, but maybe worth it
   cf. check_vpk_word ?
   Not clear : one advantage of using vpk is to avoid two calls to
   pmap.(globals) and pmap.(locals)
   Could pmap.(globlals) and pmap.(locals) directly return sub_regions ?
*)
Definition check_gvalid rmap x : option (sub_region * ByteSet.t) :=
  if is_glob x then 
    omap (fun '(_, ws) =>
      let sr := sub_region_glob x.(gv) ws in
      let bytes := ByteSet.full (interval_of_zone sr.(sr_zone)) in
      (sr, bytes)) (Mvar.get pmap.(globals) (gv x))
  else
    let sr := Mvar.get rmap.(var_region) x.(gv) in
    match sr with
    | Some sr =>
      let bytes := get_var_bytes rmap.(region_var) sr.(sr_region) x.(gv) in
      Some (sr, bytes)
    | _ => None
    end.

(* wfr_get_v_mp : 
    forall x xs mp, Mmp.get rmap.(region_vars) mp = Some xs ->
                    Sv.In x xs -> Mvar.get rmap.(var_region) x = Some mp;*)
(*
Definition wfr_VALID (rmap:regions) :=
   forall x mp, Mvar.get rmap.(var_region) x = Some mp -> valid_mp mp (vtype x).
*)
Definition wfr_VAL (rmap:region_map) (s1:estate) (s2:estate) :=
  forall x sr bytes v, check_gvalid rmap x = Some (sr, bytes) -> 
    get_gvar gd s1.(evm) x = ok v ->
    eq_sub_region_val (vtype (gv x)) s2.(emem) sr bytes v.

Definition wfr_PTR (rmap:region_map) (s2:estate) :=
  forall x sr, Mvar.get (var_region rmap) x = Some sr ->
    exists pk, get_local pmap x = Some pk /\ valid_pk rmap s2 sr pk.

Class wf_rmap (rmap:region_map) (s1:estate) (s2:estate) := {  
(*   wfr_valid_mp :  wfr_VALID rmap; *)
  wfr_val : wfr_VAL rmap s1 s2;
  wfr_ptr : wfr_PTR rmap s2;
}.

Definition eq_mem_source (m1 m2:mem) := 
  forall w sz, valid_pointer m1 w sz -> read_mem m1 w sz = read_mem m2 w sz.
(*
Definition eq_not_mod (m0 m2:mem) := 
  forall ofs, 
     0 <= ofs < stk_size ->
     (forall x xofs xty, 
        local_pos x = Some(xofs, xty) -> 
        xofs + size_of xty <= ofs \/ ofs + 1 <= xofs) ->
     read_mem m0 (rsp + (wrepr _ ofs)) U8 = 
     read_mem m2 (rsp + (wrepr _ ofs)) U8.

Class valid_state (rmap:regions) (m0:mem) (s1:estate) (s2:estate) := {
   vs_val_ptr : 
      forall s w, (0 <= wunsigned w < wptr_size s) -> valid_pointer (emem s2) (wptr s + w) U8;
   vs_disj      : disjoint_ptr (emem s1);
   vs_top_frame : ohead (frames (emem s2)) = Some (rsp, stk_size);
   vs_eq_vm     : eq_vm s1.(evm) s2.(evm);
   vs_wf_region :> wf_region rmap s1 s2;
   vs_eq_mem    : eq_glob s1.(emem) s2.(emem);
   vs_eq_not_mod: eq_not_mod m0 s2.(emem);
}.
*)

Hypothesis wf_pmap0 : wf_pmap.

(* FIXME: could we put [ms] as section variable ? it should not be modified? *)
(* TODO: add comments *)
Class valid_state (rmap : region_map) (m0 : mem) (s1 s2 : estate) := {
  vs_slot_valid : slot_valid s2.(emem);
  vs_disjoint   : disjoint_source s1.(emem);
  vs_valid_incl : valid_incl s1.(emem) s2.(emem); (* is it correct? *)
  vs_unchanged  : disjoint_writable_is_constant s1.(emem) m0 s2.(emem); (* is it correct? *)
  vs_rip        : get_var (evm s2) pmap.(vrip) = ok (Vword rip);
  vs_rsp        : get_var (evm s2) pmap.(vrsp) = ok (Vword rsp);
  vs_wf_region  : wf_var_region rmap;
  vs_eq_vm      : eq_vm s1.(evm) s2.(evm);
  vs_wf_region2 :> wf_rmap rmap s1 s2;
  vs_eq_mem     : eq_mem_source s1.(emem) s2.(emem)
}.

(* -------------------------------------------------------------------------- *)

Lemma get_globalP x z : get_global pmap x = ok z <-> Mvar.get pmap.(globals) x = Some z.
Proof.
  rewrite /get_global; case: Mvar.get; last by split.
  by move=> ?;split => -[->].
Qed.

Lemma get_gvar_glob gd x vm : is_glob x -> get_gvar gd vm x = sem.get_global gd (gv x).
Proof. by rewrite /get_gvar /is_lvar /is_glob => /eqP ->. Qed.

Lemma get_gvar_nglob gd x vm : ~~is_glob x -> get_gvar gd vm x = get_var vm (gv x).
Proof. by rewrite /get_gvar /is_lvar /is_glob; case: (gs x). Qed.

Lemma cast_ptrP gd s e i : sem_pexpr gd s e >>= to_int = ok i ->
  sem_pexpr gd s (cast_ptr e) = ok (Vword (wrepr U64 i)).
Proof. by t_xrbindP => v he hi ;rewrite /cast_ptr /cast_w /= he /sem_sop1 /= hi. Qed.

Lemma cast_wordP gd s e i : 
  sem_pexpr gd s e >>= to_int = ok i ->
  exists sz (w:word sz), sem_pexpr gd s (cast_word e) = ok (Vword w) /\
                         truncate_word U64 w = ok (wrepr U64 i).
Proof.
  move=> he.
  have : exists sz (w:word sz), 
              sem_pexpr gd s (cast_ptr e) = ok (Vword w) /\
                      truncate_word U64 w = ok (wrepr U64 i). 
  + exists U64, (wrepr U64 i); split; first by apply cast_ptrP.
    by rewrite truncate_word_u.
  case: e he => // -[] // [] //=.
  move=> e he _; move: he; rewrite /sem_sop1 /=; t_xrbindP => v v' -> w.
  move=> /to_wordI [sw [w' [hsw -> ->]]] <- [<-].
  by exists sw, w'; split => //; rewrite /truncate_word hsw wrepr_unsigned.
Qed.

Lemma mk_ofsP aa sz gd s2 ofs e i :
  sem_pexpr gd s2 e >>= to_int = ok i ->
  sem_pexpr gd s2 (mk_ofs aa sz e ofs) = ok (Vword (wrepr U64 (i * mk_scale aa sz + ofs)%Z)).
Proof.
  rewrite /mk_ofs; case is_constP => /= [? [->] //| {e} e he] /=.
  rewrite /sem_sop2 /=.
  have [sz' [w [-> /= -> /=]]]:= cast_wordP he.
  by rewrite !zero_extend_u wrepr_add wrepr_mul GRing.mulrC. 
Qed.

(* this is about two ojects from [memory_example]. MOVE ? *)
Lemma validr_valid_pointer (m1:mem) p ws : is_ok (validr m1 p ws) = valid_pointer m1 p ws.
Proof.
  case: (Memory.readV m1 p ws); rewrite Memory.readP /CoreMem.read.
  + by move=> [w]; case: validr.
  by case: validr => //= _ [];eauto.
Qed.
(*
Lemma check_validP rmap x ofs len mps : 
  check_valid rmap x ofs len = ok mps <->
  (Mvar.get (var_region rmap) x = Some mps /\
   exists xs, Mmp.get (region_var rmap) mps.(mps_mp) = Some xs /\ Sv.In x xs).
Proof.
  rewrite /check_valid.
  case heq: Mvar.get => [mp' |]; last by intuition.
  case heq1 : Mmp.get => [xs | /=]; last by split => // -[] [?]; subst mp'; rewrite heq1 => -[] ?[].
  case: ifPn => /Sv_memP hin /=.
  + split => [ [?] | [[?] ]]; subst mp' => //.
    by split => //;exists xs.
  by split => // -[] [?]; subst mp'; rewrite heq1 => -[xs'] [[<-]] /hin.
Qed.
*)

Lemma mk_ofsiP s e i aa sz :
  Let x := sem_pexpr [::] s e in to_int x = ok i ->
  mk_ofsi aa sz e <> None ->
  mk_ofsi aa sz e = Some (i * mk_scale aa sz).
Proof. by case: e => //= _ [->]. Qed.

Section EXPR.
  Variables (rmap:region_map) (m0:mem) (s:estate) (s':estate).
  Hypothesis (hvalid: valid_state rmap m0 s s').

  (* If [x] is a register : it is not impacted by the presence of global
     variables per hypothesis [vm_eq_vm]
  *)
  Lemma get_var_kindP x v:
    get_var_kind pmap x = ok None -> 
    get_gvar gd (evm s) x = ok v ->
    get_gvar [::] (evm s') x = ok v.
  Proof.
    rewrite /get_var_kind; case: ifPn => hglob; first by t_xrbindP.
    case hgl : get_local => // _.
    assert (heq := vs_eq_vm hgl). 
    by rewrite !get_gvar_nglob // heq.
  Qed.

  Lemma base_ptrP sc : get_var (evm s') (base_ptr pmap sc) = ok (Vword (wbase_ptr sc)).
  Proof. by case: sc => /=; [apply: vs_rsp | apply: vs_rip]. Qed.

  (* TODO : move => in fact already exists in memory_example *)
  Lemma wsize_le_div ws1 ws2 : (ws1 <= ws2)%CMP -> (wsize_size ws1 | wsize_size ws2).
  Proof.
(*     apply memory_example.wsize_size_le. *)
    by case: ws1; case: ws2 => //= _; apply: Znumtheory.Zmod_divide.
  Qed.

  (* TODO : move *)
  (* FIXME : no way to prove that, it seems -> we should change the memory model. *)
  Lemma is_align_le x ws1 ws2 : (ws2 <= ws1)%CMP -> is_align x ws1 ->
    is_align x ws2.
  Proof.
    move=> cmp halign.
  Admitted.

  (* TODO : shorter and more elegant proof? *)
  Lemma Zland_mod z ws : Z.land z (wsize_size ws - 1) = 0 -> z mod wsize_size ws = 0.
  Proof.
    by case: ws => /=;
      set len := (wsize_size _);
      change len with (2 ^ (Z.log2 len));
      rewrite -Z.land_ones.
  Qed.

  Lemma ge0_wunsigned ws (w:word ws) : 0 <= wunsigned w.
  Proof. by case (wunsigned_range w). Qed.

  Lemma wunsigned_repr_le ws z : 0 <= z -> wunsigned (wrepr ws z) <= z. 
  Proof. by move=> hz; rewrite wunsigned_repr; apply Z.mod_le. Qed.

  (* Question : how this proof works in the case of sword ??? *)
  Lemma size_of_gt0 ty : 0 < size_of ty.
  Proof. by case: ty. Qed.

  Lemma size_slot_gt0 sl : 0 < size_slot sl.
  Proof. by apply size_of_gt0. Qed.

  Lemma wf_zone_len_gt0 z ty sl : wf_zone z ty sl -> 0 < z.(z_len).
  Proof. by move=> [? _]; have := size_of_gt0 ty; lia. Qed.

  (* probably subsumed by slot_wunsigned_addr. TODO: remove *)
  Lemma slot_wrepr sr ty : wf_sub_region sr ty ->
    wunsigned (wrepr U64 sr.(sr_zone).(z_ofs)) = sr.(sr_zone).(z_ofs).
  Proof.
    move=> hwf; rewrite wunsigned_repr -/(wbase Uptr).
    have hlen := wf_zone_len_gt0 hwf.
    have hofs := wfz_ofs hwf.
    have /ZleP hno := addr_no_overflow (wfr_slot hwf).
    have ? := @ge0_wunsigned _ (Addr sr.(sr_region).(r_slot)).
    by apply Zmod_small; lia.
  Qed.

  Lemma wunsigned_sub_region_addr sr ty : wf_sub_region sr ty ->
    wunsigned (sub_region_addr sr) = wunsigned (Addr sr.(sr_region).(r_slot)) + sr.(sr_zone).(z_ofs).
  Proof.
    move=> hwf; apply wunsigned_add.
    have hlen := wf_zone_len_gt0 hwf.
    have hofs := wfz_ofs hwf.
    have /ZleP hno := addr_no_overflow (wfr_slot hwf).
    have ? := @ge0_wunsigned _ (Addr (sr.(sr_region).(r_slot))).
    by lia.
  Qed.

(* TODO
  Lemma check_validP x ofs len mps :
    check_valid rmap x.(gv) ofs len = ok (mps) ->
*)
  Lemma check_alignP sr ty ws tt :
    wf_sub_region sr ty ->
    check_align sr ws = ok tt ->
    is_align (sub_region_addr sr) ws.
  Proof.
    move=> hwf; rewrite /check_align; t_xrbindP => ? /assertP halign /assertP /eqP halign2.
    rewrite /sub_region_addr; apply: is_align_add.
    + apply: (is_align_le halign); rewrite -(wfr_align hwf).
      by apply: slot_align; apply: (wfr_slot hwf).
    by apply is_align_mod; apply Zland_mod; rewrite (slot_wrepr hwf).
  Qed.
(*
  Lemma region_glob_wf x ofs_align :
    Mvar.get (globals pmap) x = Some ofs_align ->
    wf_region (region_glob x ofs_align).
  Proof.
    case: ofs_align=> ofs ws.
    by move=> /wf_globals [*]; rewrite /region_glob; split=> //=; apply /idP.
  Qed.
*)
  Lemma sub_region_glob_wf x ofs ws :
    wf_global x ofs ws ->
    wf_sub_region (sub_region_glob x ws) x.(vtype).
  Proof.
    move=> [*]; split.
    + by split=> //; apply /idP.
    by split=> /=; lia.
  Qed.

  Lemma get_sub_regionP x sr :
    get_sub_region rmap x = ok sr <-> Mvar.get rmap.(var_region) x = Some sr.
  Proof.
    rewrite /get_sub_region; case: Mvar.get; last by split.
    by move=> ?; split => -[->].
  Qed.

  (* TODO: should probably become size_at_ofs : Z *)
  Definition stype_at_ofs (ofs : option Z) (ty ty' : stype) :=
    if ofs is None then ty else ty'.

  (* Sans doute à généraliser pour n'importe quelle longueur *)
  (* wsize_size ws -> len *)
  Lemma wf_sub_region_sub_zone sr ty ws ofs (* len *) :
    wf_sub_region sr ty ->
    (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + wsize_size ws <= size_of ty) ->
    wf_sub_region (sub_region_at_ofs sr ofs (wsize_size ws)) (stype_at_ofs ofs ty (sword ws)).
  Proof.
    move=> hwf hofs /=; split; first by apply hwf.(wfsr_region).
    case: ofs hofs => [ofs|] /=; last by move=> _; apply hwf.
    move=> /(_ _ refl_equal) ?.
    split=> /=; first by auto with zarith.
    have hlen := hwf.(wfz_len).
    have hofs := hwf.(wfz_ofs).
    by lia.
 Qed.

  Lemma zbetween_sub_region_addr sr ty : wf_sub_region sr ty ->
    zbetween (Addr sr.(sr_region).(r_slot)) (size_slot sr.(sr_region).(r_slot))
      (sub_region_addr sr) (size_of ty).
  Proof.
    move=> hwf; rewrite /zbetween !zify (wunsigned_sub_region_addr hwf).
    have hofs := hwf.(wfz_ofs).
    have hlen := hwf.(wfz_len).
    by lia.
  Qed.

  (* TODO: move (and rename?) *)
  Lemma mem_full i : ByteSet.mem (ByteSet.full i) i.
  Proof. by apply /ByteSet.memP => k; rewrite ByteSet.fullE. Qed.

  (* The assumption on [ofs] is different from other lemmas, since we do not
     have a slot at hand. Is it a problem?
  *)
  Lemma sub_zone_at_ofs_subset z ofs len :
    (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + len <= z.(z_len)) ->
    I.subset (interval_of_zone (sub_zone_at_ofs z ofs len)) (interval_of_zone z).
  Proof.
    move=> hofs; apply /I.subsetP; rewrite /interval_of_zone /=.
    case: ofs hofs => [ofs|] /=.
    + by move=> /(_ _ refl_equal); lia.
    by move=> _; lia.
  Qed.

  Lemma subset_memi i1 i2 n :
    I.subset i1 i2 ->
    I.memi i1 n ->
    I.memi i2 n.
  Proof. by move=> /I.subsetP hsub /I.memiP hmem; apply /I.memiP; lia. Qed.

  Lemma subset_mem bytes i1 i2 :
    I.subset i1 i2 ->
    ByteSet.mem bytes i2 ->
    ByteSet.mem bytes i1.
  Proof.
    move=> hsub /ByteSet.memP hmem; apply /ByteSet.memP.
    by move=> n /(subset_memi hsub) /hmem.
  Qed.

  Lemma check_validP (x : var_i) ofs ws sr :
    let: len := wsize_size ws in
    (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + len <= size_slot x) ->
    check_valid rmap x ofs len = ok sr ->
    exists sr' bytes,
    [/\ check_gvalid rmap (mk_lvar x) = Some (sr', bytes),
    sr = sub_region_at_ofs sr' ofs len &
    let isub_ofs := interval_of_zone sr.(sr_zone) in
    ByteSet.mem bytes isub_ofs].
  Proof.
    rewrite /check_valid /check_gvalid.
    t_xrbindP=> hofs sr' /get_sub_regionP -> _ /assertP hmem <-.
    by eexists sr', _.
  Qed.

  (* TODO: this proof can be cleaned up *)
  Lemma check_vpkP x vpk ofs ws sr :
    let: len := wsize_size ws in
    (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + len <= size_slot x.(gv)) ->
(*     0 < len -> *)
    get_var_kind pmap x = ok (Some vpk) ->
    check_vpk rmap x.(gv) vpk ofs len = ok sr ->
    exists sr' bytes,
      [/\ check_gvalid rmap x = Some (sr', bytes),
      sr = sub_region_at_ofs sr' ofs len &
      let isub_ofs := interval_of_zone sr.(sr_zone) in
      ByteSet.mem bytes isub_ofs].
  Proof.
    move=> hofs; rewrite /get_var_kind /check_gvalid.
    case : (@idP (is_glob x)) => hg.
    + t_xrbindP => -[_ ws'] /get_globalP -> <- [<-] /=.
      set sr' := sub_region_glob _ _.
      set bytes := ByteSet.full _.
      exists sr', bytes; split=> //.
      apply: subset_mem; last by apply mem_full.
      by apply sub_zone_at_ofs_subset.
    by case hlocal: get_local => [pk|//] [<-] /(check_validP hofs).
  Qed.

  (* TODO : prove the same thing for all cases of pk *)
  Lemma sub_region_addr_direct x sl ofs ws z sc :
    wf_direct x sl ofs ws z sc ->
    sub_region_addr (sub_region_direct sl ws sc z) = (wbase_ptr sc + wrepr _ (ofs + z.(z_ofs)))%R.
  Proof.
    by move=> hwf; rewrite /sub_region_addr hwf.(wfd_offset) wrepr_add GRing.addrA.
  Qed.

  (* TODO : prove the same thing for all cases of pk *)
  Lemma sub_region_direct_wf x sl ofs ws z sc :
    wf_direct x sl ofs ws z sc ->
    wf_sub_region (sub_region_direct sl ws sc z) x.(vtype).
  Proof. by case. Qed.

  Lemma sub_region_addr_glob x ofs ws :
    wf_global x ofs ws ->
    sub_region_addr (sub_region_glob x ws) = (rip + wrepr _ ofs)%R.
  Proof.
    move=> hwf.
    by rewrite /sub_region_addr /sub_region_glob /= hwf.(wfg_offset) wrepr0 GRing.addr0.
  Qed.

  (* If [x] is a local variable *)
  Lemma check_mk_addr_ptr (x:var_i) aa ws xi ei e1 i1 pk sr :
    sem_pexpr [::] s' e1 >>= to_int = ok i1 ->
    get_local pmap x = Some pk ->
    valid_pk rmap s' sr pk ->
    mk_addr_ptr pmap x aa ws pk e1 = ok (xi, ei) ->
    ∃ (wx wi : u64),
      [/\ Let x := get_var (evm s') xi in to_pointer x = ok wx,
          Let x := sem_pexpr [::] s' ei in to_pointer x = ok wi
        & (sub_region_addr sr + wrepr U64 (i1 * mk_scale aa ws))%R = (wx + wi)%R].
  Proof.
    move=> he1; rewrite /mk_addr_ptr; case: pk => //.
    + move=> sl xofs xws z sc hlocal /= -> [<- <-].
      exists (wbase_ptr sc), (wrepr _ (xofs + z.(z_ofs)) + wrepr _ (i1 * mk_scale aa ws))%R.
      rewrite (mk_ofsP aa ws (xofs + z.(z_ofs)) he1) base_ptrP /= !truncate_word_u.
      split => //.
      + by rewrite wrepr_add GRing.addrC.
      by rewrite (sub_region_addr_direct (wf_locals hlocal)) GRing.addrA.
    move=> p hlocal /= hword [<- <-].
    exists (sub_region_addr sr), (wrepr _ (i1 * mk_scale aa ws)).
    by rewrite (mk_ofsP aa ws 0 he1) Z.add_0_r hword /= !truncate_word_u.
  Qed.

  (* TODO: move this *)
  Lemma arr_is_align p ws : WArray.is_align p ws -> is_align (wrepr _ p) ws.
  Proof.
    move=> /eqP h1; apply is_align_mod.
    by rewrite wunsigned_repr -/(wbase Uptr) (cut_wbase_Uptr ws) Z.mul_comm mod_pq_mod_q.
  Qed.

  (* TODO: valid_state should be maximally implicit, so that it is inferred
     automatically
  *)
  Lemma check_gvalid_wf x sr_bytes :
    check_gvalid rmap x = Some sr_bytes ->
    wf_sub_region sr_bytes.1 x.(gv).(vtype).
  Proof.
    rewrite /check_gvalid; case: (@idP (is_glob x)) => hg.
    + by case heq: Mvar.get => [[??]|//] [<-] /=; apply (sub_region_glob_wf (wf_globals heq)).
    by case heq: Mvar.get => // -[<-]; apply (vs_wf_region heq).
  Qed.

  Lemma check_mk_addr x vpk aa ws t xi ei e1 i1 ofs : 
    sem_pexpr [::] s' e1 >>= to_int = ok i1 ->
    0 <= i1 * mk_scale aa ws /\ i1 * mk_scale aa ws + wsize_size ws <= size_slot x.(gv) ->
    WArray.is_align (i1 * mk_scale aa ws) ws ->
    get_var_kind pmap x = ok (Some vpk) ->
    check_vpk_word rmap (gv x) vpk ofs ws = ok t ->
    (ofs <> None -> ofs = Some (i1 * mk_scale aa ws)) ->
    mk_addr pmap (gv x) aa ws vpk e1 = ok (xi, ei) ->
    exists sr bytes wx wi,
    [/\ check_gvalid rmap x = Some (sr, bytes),
        let sub_ofs  := sub_zone_at_ofs sr.(sr_zone) ofs (wsize_size ws) in
        let isub_ofs := interval_of_zone sub_ofs in
        ByteSet.mem bytes isub_ofs,
        get_var (evm s') xi >>= to_pointer = ok wx,
        sem_pexpr [::] s' ei >>= to_pointer = ok wi &
        (sub_region_addr sr + wrepr Uptr (i1 * mk_scale aa ws)%Z = wx + wi)%R /\
        is_align (wx + wi) ws].
  Proof.
    move=> he1 hi1 hal1; rewrite /get_var_kind /check_vpk_word /mk_addr.
    t_xrbindP => hget sr' hvpk halign hofs haddr.
    have hofs' : ∀ zofs : Z, ofs = Some zofs → 0 <= zofs ∧ zofs + wsize_size ws <= size_slot (gv x).
    + case: (ofs) hofs => [ofs'|//].
      by move=> /(_ ltac:(discriminate)) [->] _ [<-].
    have [sr [bytes [hgvalid ? hmem]]] := check_vpkP hofs' hget hvpk; subst sr'.
    have hwf := check_gvalid_wf hgvalid.
    have hal: is_align (sub_region_addr sr + wrepr _ (i1 * mk_scale aa ws)) ws.
    + move /(check_alignP (wf_sub_region_sub_zone hwf hofs')) : halign.
      case: (ofs) hofs.
      + move=> _ /(_ ltac:(discriminate)) [->].
        by rewrite /sub_region_addr wrepr_add GRing.addrA.
      by move=> _ halign; apply is_align_add => //; apply arr_is_align.
    exists sr, bytes.
    rewrite hgvalid; move: hgvalid; rewrite /check_gvalid.
    case: (@idP (is_glob x)) hget haddr => hglob.
    + t_xrbindP=> -[xofs xws] /get_globalP hget <- [<- <-] /=.
      rewrite hget => -[??]; subst sr bytes.
      exists rip, (wrepr _ xofs + wrepr _ (i1 * mk_scale aa ws))%R.
      rewrite vs_rip (mk_ofsP aa ws xofs he1) /= !truncate_word_u wrepr_add GRing.addrC.
      split=> //.
      by move: hal; rewrite (sub_region_addr_glob (wf_globals hget)) GRing.addrA.
    case heq: get_local => [pk|//] [<-] /(check_mk_addr_ptr he1 heq) haddr.
    case hsr: Mvar.get => [sr1|//] [??]; subst sr1 bytes.
    have [pk' []] := wfr_ptr hsr; rewrite heq => -[<-] /haddr [wx [wi [-> -> heq1]]].
    by exists wx, wi; split=> //; rewrite -heq1.
  Qed.

  (* TODO : ce lemme est vrai, mais est-il utile ?
     J'ai l'impression qu'on peut encore réécrire des lemmes pour utiliser
     partout sub_region_at_ofs. Ce serait plus joli et plus court, mais
     là je sèche un peu, et il faut que j'avance donc je vais laisser tel quel
     pour le moment.
  *)
  Lemma wf_sub_region_valid_pointer sr ty ofs ws :
    wf_sub_region sr ty ->
    wsize_size ws <= size_of ty ->
    (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + wsize_size ws <= size_of ty) ->
    is_align (sub_region_addr (sub_region_at_ofs sr ofs (wsize_size ws))) ws ->
    valid_pointer (emem s') (sub_region_addr (sub_region_at_ofs sr ofs (wsize_size ws))) ws.
  Proof.
    move=> hwf hty hofs hal.
    have hslot := hwf.(wfr_slot).
    have hptr := vs_slot_valid (valid_state:=hvalid) hslot.
    apply /Memory.valid_pointerP; split=> //.
    move=> k hk; apply hptr.
    apply: between_byte hk.
    + admit.
  Abort.

  Lemma wf_sub_region_valid_pointer sr ty aa ws i :
(*     vtype (gv x) = sarr n -> *)
(*     size_slot x = n -> *)
    wf_sub_region sr ty ->
    is_align (sub_region_addr sr + wrepr U64 (i * mk_scale aa ws)) ws ->
    0 <= i * mk_scale aa ws -> i * mk_scale aa ws + wsize_size ws <= size_of ty ->
    valid_pointer (emem s') (sub_region_addr sr + wrepr U64 (i * mk_scale aa ws))%R ws.
  Proof.
    move=> hwf hal hbound1 hbound2.
    have hslot := hwf.(wfr_slot).
    have hptr := vs_slot_valid (valid_state:=hvalid) hslot.
    apply /Memory.valid_pointerP; split=> //.
    move=> k hk; apply hptr.
    have hover := addr_no_overflow hslot.
    rewrite /sub_region_addr /between /= !zify -!GRing.addrA -!wrepr_add.
    set addr := (Addr _) in hptr, hover |- *.
    case: hwf.(wfsr_zone) => *. (*; rewrite /size_slot hty /= in hle.*)
    have ? := @ge0_wunsigned _ addr.
    move: hover; rewrite /no_overflow zify => hover.
    by rewrite wsize8 wunsigned_add; lia.
  Qed.

  Lemma get_arr_read_mem (n:positive) (t : WArray.array n) sr bytes ofs aa ws i w x:
    vtype (gv x) = sarr n ->
    eq_sub_region_val (sarr n) (emem s') sr bytes (Varr t) ->
    check_gvalid rmap x = Some (sr, bytes) ->
    ByteSet.mem bytes (interval_of_zone (sub_zone_at_ofs sr.(sr_zone) ofs (wsize_size ws))) ->
    (ofs <> None -> ofs = Some (i * mk_scale aa ws)) ->
    WArray.get aa ws t i = ok w ->
    is_align (sub_region_addr sr + wrepr U64 (i * mk_scale aa ws)) ws ->
    read_mem (emem s') (sub_region_addr sr + wrepr U64 (i * mk_scale aa ws)) ws = ok w.
  Proof.
    move=> hty heq hgvalid hmem hofs hget hal.
    rewrite Memory.readP /CoreMem.read.
    have [hbound1 hbound2 _] := WArray.get_bound hget.
    have hty': size_slot x.(gv) = n.
    + by rewrite hty.
    rewrite -hty' in hbound2.
    have := wf_sub_region_valid_pointer (check_gvalid_wf hgvalid) hal hbound1 hbound2.
    rewrite -validr_valid_pointer => /is_okP [?] /= => hv; rewrite hv.
    case: heq => t' [] /Varr_inj [] heq.
    rewrite (Eqdep_dec.UIP_dec Pos.eq_dec heq erefl) /= => {heq} ? hgr;subst t'.
    move: (hget);rewrite /WArray.get /CoreMem.read; t_xrbindP => ? _ <-.
    do 2 f_equal; rewrite /CoreMem.uread.
    apply eq_map_ziota => k hk /=.
    have [v hget8]:= WArray.get_get8 AAscale hget hk.
    have /WArray.get_uget -> := hget8.
    move /hgr: hget8; rewrite Memory.readP /CoreMem.read.
    have h: 0 <= i * mk_scale aa ws + k ∧ i * mk_scale aa ws + k < n by lia.
    have h1: ByteSet.memi bytes (sr.(sr_zone).(z_ofs) + (i * mk_scale aa ws + k)).
    + move /ByteSet.memP : hmem; apply.
      rewrite /I.memi /= !zify.
      case: ofs hofs => [ofs|_].
      + by move=> /(_ ltac:(discriminate)) [->] /=; lia.
      have /= hwf := check_gvalid_wf hgvalid.
      have hlen := hwf.(wfz_len).
      by rewrite hty /= in hlen; lia.
    move=> /(_ h h1){h h1}; t_xrbindP => ? hvr.
    by rewrite CoreMem.uread8_get addE wrepr_add GRing.addrA.
  Qed.

  Let X e : Prop :=
    ∀ e' v,
      alloc_e pmap rmap e = ok e' →
      sem_pexpr gd s e = ok v →
      sem_pexpr [::] s' e' = ok v.

  Let Y es : Prop :=
    ∀ es' vs,
      alloc_es pmap rmap es = ok es' →
      sem_pexprs gd s es = ok vs →
      sem_pexprs [::] s' es' = ok vs.

  Lemma check_varP (x:var_i) t: 
    check_var pmap x = ok t -> 
    get_var_kind pmap (mk_lvar x) = ok None.
  Proof. by rewrite /check_var /get_var_kind /=; case: get_local. Qed.


(* TODO: open GRing *)
  Lemma check_e_esP : (∀ e, X e) * (∀ es, Y es).
  Proof.
    apply: pexprs_ind_pair; subst X Y; split => //=.
    + by move=> ?? [<-] [<-].
    + move=> e he es hes ??; t_xrbindP => e' /he{he}he es' /hes{hes}hes <- /=.
      by move=> v /he -> vs /hes -> <-.
    + by move=> z ?? [<-] [<-].
    + by move=> b ?? [<-] [<-].
    + by move=> n ?? [<-] [<-].
    + move=> x e' v; t_xrbindP => -[ vpk | ] hgvk; last first.
      + by move=> [<-]; apply: get_var_kindP hgvk.
      case hty: is_word_type => [ws | //]; move /is_word_typeP in hty.
      t_xrbindP => ? hcheck [xi ei] haddr <- /=.
      have h0: Let x := sem_pexpr [::] s' 0 in to_int x = ok 0 by done.
      have h1: 0 <= 0 ∧ 0 * mk_scale AAdirect ws + wsize_size ws <= size_slot (gv x).
      + by rewrite hty /=; lia.
      have h2: WArray.is_align (0 * mk_scale AAdirect ws) ws by [].
      have h3: Some 0 ≠ None → Some 0 = Some (0 * mk_scale AAdirect ws) by [].
      have [sr [bytes [wx [wi [hgvalid /= hmem -> -> /= [haddr2 halign]]]]]] :=
        check_mk_addr h0 h1 h2 hgvk hcheck h3 haddr.
      move=> /(wfr_val hgvalid); rewrite hty /=.
      move=> [w [-> hread]]; rewrite -haddr2 wrepr0 GRing.addr0 hread //.
      by rewrite /interval_of_zone /= Z.add_0_r in hmem.
    + move=> aa sz x e1 he1 e' v he'; apply: on_arr_gvarP => n t hty /= hget.
      t_xrbindP => i vi /he1{he1}he1 hvi w hw <-.
      move: he'; t_xrbindP => e1' /he1{he1}he1'.
      have h0 : sem_pexpr [::] s' e1' >>= to_int = ok i.
      + by rewrite he1'.
      move=> [vpk | ]; last first.
      + by move => /get_var_kindP -/(_ _ hget) h [<-] /=; rewrite h /= h0 /= hw.
      t_xrbindP => hgvk ? hcheck [xi ei] haddr <- /=.
      have [h1 h2 h3] := WArray.get_bound hw.
      have h4 : 0 <= i * mk_scale aa sz /\ i * mk_scale aa sz + wsize_size sz <= size_slot x.(gv).
      + by rewrite hty.
      have [sr [bytes [wx [wi [hgvalid /= hmem -> -> /= [haddr2 halign]]]]]] :=
        check_mk_addr h0 h4 h3 hgvk hcheck (mk_ofsiP h0) haddr.
      assert (h:= wfr_val hgvalid hget); move: h; rewrite hty => h.
      rewrite -haddr2 in halign |- *.
      by rewrite (get_arr_read_mem hty h hgvalid hmem (mk_ofsiP h0) hw halign).
    + move=> sz1 v1 e1 IH e2 v.
      t_xrbindP => ? /check_varP hc e1' /IH hrec <- wv1 vv1 /= hget hto' we1 ve1.
      move=> /hrec -> hto wr hr ?; subst v.
      have := get_var_kindP hc hget; rewrite /get_gvar /= => -> /=.
      by rewrite hto' hto /= -(vs_eq_mem (read_mem_valid_pointer hr)) hr.
    + move=> o1 e1 IH e2 v.
      by t_xrbindP => e1' /IH hrec <- ve1 /hrec /= ->.
    + move=> o1 e1 H1 e1' H1' e2 v.
      by t_xrbindP => e1_ /H1 hrec e1'_ /H1' hrec' <- ve1 /hrec /= -> /= ve2 /hrec' ->.
    + move => e1 es1 H1 e2 v.
      t_xrbindP => es1' /H1{H1}H1 <- vs /H1{H1} /=.
      by rewrite /sem_pexprs => ->.
    move=> t e He e1 H1 e1' H1' e2 v.
    t_xrbindP => e_ /He he e1_ /H1 hrec e1'_ /H1' hrec' <-.
    by move=> b vb /he /= -> /= -> ?? /hrec -> /= -> ?? /hrec' -> /= -> /= ->.
  Qed.

  Definition alloc_eP := check_e_esP.1.
  Definition alloc_esP := check_e_esP.2.

End EXPR.

Lemma check_diffP x t : check_diff pmap x = ok t -> ~Sv.In x (vnew pmap).
Proof. by rewrite /check_diff; case:ifPn => /Sv_memP. Qed.

Lemma get_var_eq x vm v : get_var vm.[x <- v] x = on_vu (pto_val (t:=vtype x)) undef_error v.
Proof. by rewrite /get_var Fv.setP_eq. Qed.

Lemma get_var_neq x y vm v : x <> y -> get_var vm.[x <- v] y = get_var vm y.
Proof. by move=> /eqP h; rewrite /get_var Fv.setP_neq. Qed.

Lemma get_var_set_eq vm1 vm2 (x y : var) v: 
  get_var vm1 y = get_var vm2 y ->
  get_var vm1.[x <- v] y = get_var vm2.[x <- v] y.
Proof.
  by case:( x =P y) => [<- | hne]; rewrite !(get_var_eq, get_var_neq).
Qed.

Lemma is_lvar_is_glob x : is_lvar x = ~~is_glob x.
Proof. by case: x => ? []. Qed.

Lemma get_gvar_eq gd x vm v : 
  ~is_glob x -> get_gvar gd vm.[gv x <- v] x = on_vu (pto_val (t:=vtype (gv x))) undef_error v.
Proof. 
  by move=> /negP => h; rewrite /get_gvar is_lvar_is_glob h get_var_eq.
Qed.

Lemma get_gvar_neq gd (x:var) y vm v : (~is_glob y -> x <> (gv y)) -> get_gvar gd vm.[x <- v] y = get_gvar gd vm y.
Proof. 
  move=> h; rewrite /get_gvar is_lvar_is_glob. 
  by case: negP => // hg; rewrite get_var_neq //; apply h.
Qed.

Lemma get_gvar_set_eq gd vm1 vm2 x y v: 
  get_gvar gd vm1 y = get_gvar gd vm2 y ->
  get_gvar gd vm1.[x <- v] y = get_gvar gd vm2.[x <- v] y.
Proof.
  case : (@idP (is_glob y)) => hg; first by rewrite !get_gvar_neq.
  case:( x =P (gv y)) => heq; last by rewrite !get_gvar_neq.
  by move: v; rewrite heq => v; rewrite !get_gvar_eq.
Qed.

Lemma get_localn_checkg_diff rmap sr_bytes s2 x y : 
  get_local pmap x = None ->
  wfr_PTR rmap s2 ->
  check_gvalid rmap y = Some sr_bytes ->
  (~is_glob y -> x <> (gv y)).
Proof.
  rewrite /check_gvalid; case:is_glob => // hl hwf.
  case heq: Mvar.get => [sr' | // ] _ _.
  by have /hwf [pk [hy _]] := heq; congruence.
Qed.

Lemma valid_state_set_var rmap m0 s1 s2 x v:
  valid_state rmap m0 s1 s2 ->
  get_local pmap x = None ->
  ¬ Sv.In x (vnew pmap) ->
  valid_state rmap m0 (with_vm s1 (evm s1).[x <- v]) (with_vm s2 (evm s2).[x <- v]).
Proof.
  case: s1 s2 => mem1 vm1 [mem2 vm2] [/=] hvalid hdisj hincl hunch hrip hrsp hwfr heqvm hwfr2 heqmem hget hnin.
  constructor => //=.
  + by rewrite get_var_neq //; assert (h:=rip_in_new); SvD.fsetdec.
  + by rewrite get_var_neq //; assert (h:=rsp_in_new); SvD.fsetdec.
  + by move=> y hy; apply get_var_set_eq; apply heqvm.
  rewrite /with_vm /=; case: hwfr2 => hval hptr.
  constructor => //=.
  + move=> y sr bytes vy hy; have ? := get_localn_checkg_diff hget hptr hy.
    by rewrite get_gvar_neq //; apply hval.
  move=> y mp hy; have [pk [hgety hpk]]:= hptr y mp hy; exists pk; split => //.
  case: pk hgety hpk => //= yp hyp.
  assert (h := wfr_new (wf_locals hyp)).
  by rewrite get_var_neq //; SvD.fsetdec.
Qed.
(*
(* Qu'est-ce que rset_word ? *)
Lemma set_wordP rmap x sr ws rmap': 
  set_word rmap x sr ws = ok rmap' ->
  exists sr',
  check_gvalid 
  [/\ Mvar.get (var_region rmap) x = Some sr,
      mp_s mp = MSstack, 
      is_align (wrepr Uptr (mp_ofs mp)) ws &
      wf_region
      Align
      rmap' = rset_word rmap x mp]. 
Proof.
  rewrite /set_word.
  case heq : Mvar.get => [ [[] ofs] | ] //=.
  t_xrbindP => ? /assertP hal <-.
  by eexists; split; first reflexivity.
Qed.
*)

Lemma wsize_size_le ws ws': (ws ≤ ws')%CMP -> (wsize_size ws <= wsize_size ws').
Proof. by case: ws ws' => -[]. Qed.

Lemma size_of_le ty ty' : subtype ty ty' -> size_of ty <= size_of ty'.
Proof.
  case: ty => [||p|ws]; case:ty' => [||p'|ws'] //.
  + by move=> /ZleP.
  by apply wsize_size_le.
Qed.
(*
Lemma check_gvalid_rset_word rmap x y mp mpy: 
  mp_s mp = MSstack ->
  Mvar.get (var_region rmap) x = Some mp ->
  check_gvalid (rset_word rmap x mp) y = Some mpy ->
  [/\ ~is_glob y, x = (gv y) & mp = mpy] \/ 
  [/\ (~is_glob y -> x <> gv y), mp <> mpy &check_gvalid rmap y = Some mpy].
Proof.
  rewrite /check_gvalid /rset_word => hmps hgx.
  case:ifPn => ?.
  + move=> h; right;split => //.
    by case: Mvar.get h => // ? [<-] => ?; subst mp.
  case heq : check_valid => [mp1 | //] [?]; subst mp1.
  move:heq; rewrite check_validP => /= -[hgy [xs []]].
  rewrite Mmp.setP; case: eqP => [? [?]| ].
  + by subst mpy xs => /SvD.F.singleton_iff ?; left.
  move=> hd hg /Sv_memP hin; right; split => //.
  + by move=> _ ?; subst x; apply hd; move: hgy;rewrite hgx => -[].
  by rewrite /check_valid hgy hg hin.
Qed.

Lemma get_global_pos x ofs: 
  get_global pmap x = ok ofs ->
  global_pos x = Some (ofs, vtype x).
Proof. by rewrite get_globalP /global_pos => ->. Qed.

Lemma get_local_pos x ofs:
  get_local pmap x = Some (Pstack ofs) ->
  local_pos x = Some (ofs, vtype x).
Proof. by rewrite /local_pos => ->. Qed.

Lemma valid_mp_bound mp ty : 
  valid_mp mp ty ->
  0 <= mp_ofs mp ∧ 
  mp_ofs mp + size_of ty <= wptr_size (mp_s mp).
Proof.
  move=> [x [/size_of_le hsub hv]].
  case: eqP hv => heq.
  + rewrite heq => /get_global_pos hgp. 
    assert (h:= wfg_ofs wf_globals hgp); rewrite /wptr_size /=; lia.
  move=> /get_local_pos hgx.
  assert (h:= wfg_ofs wf_locals hgx).
  have -> : mp_s mp = MSstack by case: (mp_s mp) heq.
  rewrite /wptr_size /=; lia.
Qed.

Lemma valid_mp_addr mp ty: 
  valid_mp mp ty ->
  wunsigned (mp_addr mp) = wunsigned (wptr (mp_s mp)) + (mp_ofs mp).
Proof.
  move=> /valid_mp_bound; rewrite /mp_addr => h.
  apply wunsigned_add; have ? := gt0_size_of ty.
  have := @ge0_wunsigned Uptr (wptr (mp_s mp)).
  by case: (mp_s mp) h; rewrite /wptr /wptr_size /=; lia.
Qed.

Lemma valid_mp_addr_bound mp ty: 
  valid_mp mp ty ->
  wunsigned (wptr (mp_s mp)) <= wunsigned (mp_addr mp) /\
  wunsigned (mp_addr mp) + size_of ty <= wunsigned (wptr (mp_s mp)) + wptr_size (mp_s mp).
Proof.
  move=> h; rewrite (valid_mp_addr h); have := (valid_mp_bound h); lia.
Qed.

Lemma ms_bound s : wunsigned (wptr s) + wptr_size s <= wbase Uptr.
Proof. by case: s. Qed.
*)

(* TODO : move (and rename?) *)
Lemma zbetween_refl p sz : zbetween p sz p sz.
Proof. by rewrite /zbetween !zify; lia. Qed.

(* TODO : move *)
Lemma disjoint_zrange_incl p1 s1 p2 s2 p1' s1' p2' s2' :
  zbetween p1 s1 p1' s1' ->
  zbetween p2 s2 p2' s2' ->
  disjoint_zrange p1 s1 p2 s2 ->
  disjoint_zrange p1' s1' p2' s2'.
Proof.
  rewrite /zbetween /disjoint_zrange /no_overflow !zify.
  by move=> ?? [/ZleP ? /ZleP ? ?]; split; rewrite ?zify; lia.
Qed.

(* TODO : move *)
Lemma disjoint_zrange_incl_l p1 s1 p2 s2 p1' s1' :
  zbetween p1 s1 p1' s1' ->
  disjoint_zrange p1 s1 p2 s2 ->
  disjoint_zrange p1' s1' p2 s2.
Proof. by move=> ?; apply disjoint_zrange_incl=> //; apply zbetween_refl. Qed.

(* TODO : move *)
Lemma disjoint_zrange_incl_r p1 s1 p2 s2 p2' s2' :
  zbetween p2 s2 p2' s2' ->
  disjoint_zrange p1 s1 p2 s2 ->
  disjoint_zrange p1 s1 p2' s2'.
Proof. by move=> ?; apply disjoint_zrange_incl=> //; apply zbetween_refl. Qed.

Lemma no_overflow_incl p1 sz1 p2 sz2 :
  zbetween p1 sz1 p2 sz2 ->
  no_overflow p1 sz1 ->
  no_overflow p2 sz2.
Proof. by rewrite /zbetween /no_overflow !zify; lia. Qed.

Lemma no_overflow_sub_region_addr sr ty :
  wf_sub_region sr ty ->
  no_overflow (sub_region_addr sr) (size_of ty).
Proof.
  move=> hwf; apply (no_overflow_incl (zbetween_sub_region_addr hwf)).
  by apply (addr_no_overflow hwf.(wfr_slot)).
Qed.

(* Could be an alternative definition for [between_byte]. They are equivalent
   thanks to [zbetween_trans] and [zbetween_refl].
*)
Lemma between_byte pstk sz i  :
  no_overflow pstk sz →
  0 <= i /\ i < sz ->
  between pstk sz (pstk + wrepr U64 i) U8.
Proof.
  rewrite /between /zbetween /no_overflow !zify wsize8 => novf i_range.
  rewrite wunsigned_add; first lia.
  by move: (wunsigned_range pstk); lia.
Abort.

Lemma disjoint_zrange_byte p1 ws p2 sz i :
  disjoint_zrange p1 (wsize_size ws) p2 sz ->
  0 <= i /\ i < sz ->
  disjoint_range p1 ws (p2 + wrepr _ i) U8.
Proof.
  move=> hd hrange.
  case: (hd) => _ hover _.
  apply: disjoint_zrange_incl_r hd.
  apply: (between_byte hover) => //.
  by apply zbetween_refl.
Qed.

Lemma disjoint_zrange_eq_sub_region_val p sr bytes ty mem1 mem2 ws w v: 
  wf_sub_region sr ty ->
  disjoint_zrange p (wsize_size ws) (sub_region_addr sr) (size_of ty) ->
  write_mem mem1 p ws w = ok mem2 ->
  eq_sub_region_val ty mem1 sr bytes v ->
  eq_sub_region_val ty mem2 sr bytes v.
Proof.
  case: ty => // [pt | ws']; rewrite /size_of => hwf hd hw /=.
  + move=> [t] [-> heq]; exists t; split => // off hoff hmem v1 /(heq _ hoff hmem) <-.
    apply: (Memory.writeP_neq hw).
    by apply (disjoint_zrange_byte hd).
  move=> [w1] [-> heq]; exists w1; split => // hmem; rewrite -(heq hmem).
  by apply: (Memory.writeP_neq hw).
Qed.
(*
Lemma valid_mp_disjoint mp1 mp2 ty1 ty2: 
  wf_sub_region mp1 ty1 -> 
  wf_sub_region mp2 ty2 ->
  mp1 <> mp2 -> 
  wunsigned (sub_region_addr mp1) + size_of ty1 <= wunsigned (sub_region_addr mp2) ∨ 
  wunsigned (sub_region_addr mp2) + size_of ty2 <= wunsigned (sub_region_addr mp1).
Proof.
  move=> h1 h2; rewrite (wunsigned_sub_region_addr h1) (wunsigned_sub_region_addr h2).
  case: mp1 mp2 h1 h2 => [ms1 ofs1] [ms2 ofs2].
  move=> [x1 [/size_of_le hle1 /= hget1]] [x2 [/size_of_le hle2 /= hget2]].
  have ? := gt0_size_of (vtype x1); have ? := gt0_size_of (vtype x2).
  assert (wfg := wf_globals); assert (wfl := wf_locals).
  case: ms1 hget1 => /= [/get_global_pos | /get_local_pos] h1.
  + have hg1 := wfg_ofs wfg h1; have hg2 := wfg_disj wfg _ h1.
    case: ms2 hget2 => /= [/get_global_pos | /get_local_pos] h2 hd.
    + have hxd: x1 <> x2 by move=> h;apply hd; move: h2; rewrite -h h1 => -[->].
      by have:= hg2 _ _ _ hxd h2; lia.
    have hl2:=  wfg_ofs wfl h2; rewrite /wptr /wptr_size /=; lia.
  have hl1 := wfg_ofs wfl h1; have hl2 := wfg_disj wfl _ h1.
  case: ms2 hget2 => /= [/get_global_pos | /get_local_pos] h2 hd.
  + have hg2:=  wfg_ofs wfg h2; rewrite /wptr /wptr_size /=; lia.
  have hxd: x1 <> x2 by move=> h;apply hd; move: h2; rewrite -h h1 => -[->].
  by have:= hl2 _ _ _ hxd h2; lia.
Qed.
*)

(* TODO: move *)
Lemma disjoint_zrange_sym p1 sz1 p2 sz2 :
  disjoint_zrange p1 sz1 p2 sz2 ->
  disjoint_zrange p2 sz2 p1 sz1.
Proof.
  rewrite /disjoint_zrange; move=> [*]; split=> //; lia.
Qed.

Lemma eq_mp_val_write_disj rmap m0 s1 s2 sr ty sry ty' mem2 bytes v ws w p:
  valid_state rmap m0 s1 s2 ->
  wf_sub_region sr ty ->
  wf_sub_region sry ty' ->
  sr.(sr_region).(r_slot) <> sry.(sr_region).(r_slot) ->
  sry.(sr_region).(r_writable) ->
  between (sub_region_addr sr) (size_of ty) p ws ->
  write_mem (emem s2) p ws w = ok mem2 ->
  eq_sub_region_val ty' (emem s2) sry bytes v →
  eq_sub_region_val ty' mem2 sry bytes v.
Proof.
  move=> hvs hwf hwfy hd hw hb.
  apply: disjoint_zrange_eq_sub_region_val => //.
  apply: (disjoint_zrange_incl_l hb).
  apply (disjoint_zrange_incl_l (zbetween_sub_region_addr hwf)).
  apply (disjoint_zrange_incl_r (zbetween_sub_region_addr hwfy)).
  apply disjoint_zrange_sym.
  apply disjoint_writable.
  apply hwfy.(wfr_slot).
  apply hwf.(wfr_slot). congruence. by rewrite hwfy.(wfr_writable).
Qed.
(*
Lemma get_local_pos_sptr x ofs : get_local pmap x = Some (Pstkptr ofs) -> local_pos x = Some(ofs, sword Uptr).
Proof. by rewrite /local_pos => ->. Qed.

Lemma sptr_addr x ofs: 
  local_pos x = Some (ofs, sword Uptr) ->
  wunsigned (mp_addr {| mp_s := MSstack; mp_ofs := ofs |}) = wunsigned rsp + ofs.
Proof.
  move=> h; assert (h1:= wfg_ofs wf_locals h).
  rewrite /mp_addr /wptr /=; apply wunsigned_add.
  move: (gt0_size_of (sword Uptr)) (@ge0_wunsigned Uptr rsp); lia.
Qed.

Lemma sptr_addr_bound x ofs:
  local_pos x = Some (ofs, sword Uptr) ->
  wunsigned rsp <= wunsigned (mp_addr {| mp_s := MSstack; mp_ofs := ofs |}) /\
  wunsigned (mp_addr {| mp_s := MSstack; mp_ofs := ofs |}) + wsize_size Uptr <= wunsigned rsp + stk_size.
Proof.
  move=> h; rewrite (sptr_addr h).
  assert (h1:= wfg_ofs wf_locals h); move: h1 => /=; lia.
Qed.
*)

Lemma sub_region_pk_valid rmap s sr pk :
  sub_region_pk pk = ok sr -> valid_pk rmap s sr pk.
Proof. by case: pk => // v ofs ws z [|//] [<-]. Qed.

Lemma sub_region_pk_wf x pk sr ws :
  get_local pmap x = Some pk ->
  x.(vtype) = sword ws ->
  sub_region_pk pk = ok sr ->
  wf_sub_region sr x.(vtype).
Proof.
  case: pk => // v ofs ws' z [|//] /wf_locals /= hget hty /= [<-].
  case: hget => *.
  by rewrite /sub_region_addr /sub_region_stack; split.
Qed.

Lemma sub_region_stkptr_wf y s ofs ws z f :
  wf_stkptr y s ofs ws z f ->
  wf_sub_region (sub_region_stkptr s ws z) sptr.
Proof. by case. Qed.


Lemma get_bytes_map_setP rv r r' bm :
  get_bytes_map r (Mr.set rv r' bm) = if r' == r then bm else get_bytes_map r rv.
Proof. by rewrite /get_bytes_map Mr.setP; case: eqP. Qed.

Lemma get_bytes_setP bm x x' bytes :
  get_bytes x (Mvar.set bm x' bytes) = if x' == x then bytes else get_bytes x bm.
Proof. by rewrite /get_bytes Mvar.setP; case: eqP. Qed.

Lemma get_bytes_clear x i bm :
  get_bytes x (clear_bytes_map i bm) =
  ByteSet.remove (get_bytes x bm) i.
Proof.
  rewrite /clear_bytes_map /get_bytes.
  by rewrite Mvar.mapP; case: Mvar.get => //=; rewrite remove_empty.
Qed.

(* TODO: factorize set_sub_region and similar *)
Lemma get_var_bytes_set_sub_region rmap x sr r y :
  get_var_bytes (set_sub_region rmap x sr) r y =
    if sr.(sr_region) != r then
      get_var_bytes rmap r y
    else
      let i := interval_of_zone sr.(sr_zone) in
      if x == y then
        ByteSet.full i
      else
        let bytes := get_var_bytes rmap r y in
        ByteSet.remove bytes i.
Proof.
  rewrite /set_sub_region /get_var_bytes /=.
  rewrite get_bytes_map_setP.
  case: eqP => [->|heq] //=.
  rewrite get_bytes_setP.
  by case: ifP => // _; rewrite get_bytes_clear.
Qed.

Lemma check_gvalid_set_sub_region rmap x sr y sry bytes :
  check_gvalid (set_sub_region rmap x sr) y = Some (sry, bytes) ->
    [/\ is_glob y & check_gvalid rmap y = Some (sry, bytes)] \/
    [/\ ~ is_glob y, x <> gv y, Mvar.get rmap.(var_region) y.(gv) = Some sry &
        bytes = get_var_bytes (set_sub_region rmap x sr) sry.(sr_region) y.(gv)] \/
    [/\ ~ is_glob y, x = gv y, sr = sry & bytes = ByteSet.full (interval_of_zone sr.(sr_zone))].
Proof.
  rewrite /check_gvalid.
  case: (@idP (is_glob y)) => hg.
  + by case heq: Mvar.get => [[ofs ws]|//] [<- <-]; left; split.
  rewrite Mvar.setP; case: eqP => heq.
  + move=> [<- <-].
    right; right; split=> //.
    rewrite get_var_bytes_set_sub_region.
    by case: eqP => //=; case: eqP.
  case heq': Mvar.get => [sr'|//] [? <-]; subst sr'.
  by right; left; split.
Qed.

(* TODO: use get_bytes' and simplify the proof (or remove this lemma) *)
Lemma check_stack_ptr_neq rmap x sr s w ofs f :
  sr.(sr_region).(r_slot) <> s ->
  check_stack_ptr (set_sub_region rmap x sr) s w ofs f =
  check_stack_ptr rmap s w ofs f.
Proof.
  move=> hneq; rewrite /check_stack_ptr.
  have := get_var_bytes_set_sub_region rmap x sr {| r_slot := s; r_align := w; r_writable := true |} f.
  rewrite /get_var_bytes /= => ->.
  by case: eqP => /=; case: sr.(sr_region) hneq => /=; congruence.
Qed.

Definition disjoint_intervals i1 i2 := I.is_empty (I.inter i1 i2).

Lemma interE i1 i2 n : I.memi (I.inter i1 i2) n = I.memi i1 n && I.memi i2 n.
Proof.
  by rewrite /I.inter /I.memi /=; apply /idP/idP; rewrite !zify; lia.
Qed.

Lemma mem_remove bytes i i' :
  ByteSet.mem (ByteSet.remove bytes i) i' -> ByteSet.mem bytes i' /\ disjoint_intervals i i'.
Proof.
  move=> /ByteSet.memP hsubset; split.
  + apply /ByteSet.memP => n /hsubset.
    by rewrite ByteSet.removeE => /andP [].
  rewrite /disjoint_intervals; apply /I.is_emptyP.
  move => n; apply /negP; rewrite interE.
  move=> /andP [hmem1 hmem2].
  by move: (hsubset _ hmem2); rewrite ByteSet.removeE hmem1 andbF.
Qed.

(* FIXME: why are we using CMP on Z ?? *)
Lemma Zcmp_le i1 i2 : (i1 <= i2)%CMP = (i1 <=? i2)%Z.
Proof.
  rewrite /cmp_le /gcmp /Mz.K.cmp /Z.leb -Zcompare_antisym.
  by case: Z.compare.
Qed.

(* devrait-on remplacer les deux hypothèses par des wf_zone ? *)
Lemma disjoint_interval_of_zone z1 z2 :
  0 < z1.(z_len) -> 0 < z2.(z_len) ->
  disjoint_intervals (interval_of_zone z1) (interval_of_zone z2) =
  disjoint_zones z1 z2.
Proof.
  move=> hlen1 hlen2.
  rewrite /disjoint_intervals /interval_of_zone /disjoint_zones /I.is_empty /=.
  apply /idP/idP; rewrite !Zcmp_le !zify; lia.
Qed.

(* TODO: disjoint_zones is too strong in general, we should weaken this lemma,
   otherwise it is useless.
*)
Lemma disjoint_zones_disjoint_zrange sr1 ty1 sr2 ty2 :
  wf_sub_region sr1 ty1 ->
  wf_sub_region sr2 ty2 ->
  sr1.(sr_region) = sr2.(sr_region) ->
  disjoint_zones sr1.(sr_zone) sr2.(sr_zone) ->
  disjoint_zrange (sub_region_addr sr1) (size_of ty1) (sub_region_addr sr2) (size_of ty2).
Proof.
  move=> hwf1 hwf2 heq.
  have := addr_no_overflow (wfr_slot hwf1).
  have := addr_no_overflow (wfr_slot hwf2).
  rewrite /disjoint_zones /disjoint_range /disjoint_zrange /no_overflow !Zcmp_le !zify.
  rewrite (wunsigned_sub_region_addr hwf1) (wunsigned_sub_region_addr hwf2).
  have /= := wfz_len hwf1.
  have /= := wfz_len hwf2.
  have := wfz_ofs hwf1.
  have := wfz_ofs hwf2.
  rewrite heq.
  by split; rewrite ?zify; lia.
Qed.

(* I tried to avoid proof duplication with this auxiliary lemma. But there is
   some duplication even in the proof of this lemma...
*)
Lemma valid_pk_set_sub_region rmap m0 s1 s2 x sr p ws w mem2 y pk sry :
  valid_state rmap m0 s1 s2 ->
  wf_sub_region sr x.(vtype) ->
  ~ Sv.In x pmap.(vnew) ->
  between (sub_region_addr sr) (size_slot x) p ws ->
  write_mem (emem s2) p ws w = ok mem2 ->
  wf_local y pk ->
  valid_pk rmap s2 sry pk ->
  valid_pk (set_sub_region rmap x sr) (with_mem s2 mem2) sry pk.
Proof.
  move=> hvs hwf hnin hb hw hlocal hpk.
  case: pk hlocal hpk => //= s ofs ws' z f hlocal hpk.
  have hwf2 := sub_region_stkptr_wf hlocal.
  rewrite /check_stack_ptr; t_xrbindP => _ /assertP; rewrite get_var_bytes_set_sub_region.
  case: eqP => heq /=.
  + case: eqP => heq2.
    + by have := hlocal.(wfs_new); congruence.
    move=> /mem_remove [].
    rewrite (disjoint_interval_of_zone (wf_zone_len_gt0 hwf) (wf_zone_len_gt0 hwf2)).
    move=> hmem hdisj _.
    rewrite -hpk; last by rewrite /check_stack_ptr hmem.
    apply: (Memory.writeP_neq hw).
    apply (disjoint_zrange_incl_l hb).
    by apply (disjoint_zones_disjoint_zrange hwf hwf2).
  move=> hmem _.
  rewrite -hpk; last by rewrite /check_stack_ptr hmem.
  apply: (Memory.writeP_neq hw).
  apply (disjoint_zrange_incl_l hb).
  apply: disjoint_zrange_incl.
  + by apply (zbetween_sub_region_addr hwf).
  + by apply (zbetween_sub_region_addr hwf2).
  apply disjoint_zrange_sym.
  have hwritable := hlocal.(wfs_writable).
  apply (disjoint_writable hwf2.(wfr_slot) hwf.(wfr_slot)) => //.
  (* TODO: this proof is not so elegant *)
  have := hlocal.(wfs_align).
  have := hwf.(wfr_align).
  have := hwf.(wfr_writable).
  case: sr.(sr_region) heq => /=; congruence.
Qed.

(* TODO : points à discuter
   - comparaison Z avec %CMP
   - sub_region_stkptr ?? -> z ou {z_ofs; wsize_size U64 }
   - pk on fait les choses en double ?
   - a-t-on besoin d'introduire p et ws ?
*)
Lemma wfr_PTR_set_sub_region rmap m0 s1 s2 x pk sr p ws w mem2 :
  valid_state rmap m0 s1 s2 ->
  get_local pmap x = Some pk ->
  wf_sub_region sr x.(vtype) ->
  valid_pk rmap s2 sr pk ->
  ~ Sv.In x pmap.(vnew) ->
  between (sub_region_addr sr) (size_slot x) p ws ->
  write_mem (emem s2) p ws w = ok mem2 ->
  wfr_PTR rmap s2 ->
  wfr_PTR (set_sub_region rmap x sr) (with_mem s2 mem2).
Proof.
  move=> hvs hget hwf hpk hnin hb hw hwfr y sry.
  rewrite Mvar.setP; case: eqP.
  + move=> <- [<-].
    exists pk; split=> //.
    by apply (valid_pk_set_sub_region hvs hwf hnin hb hw (wf_locals hget) hpk).
  move=> _ /hwfr {pk hget hpk} [pk [hget hpk]].
  exists pk; split=> //.
  by apply (valid_pk_set_sub_region hvs hwf hnin hb hw (wf_locals hget) hpk).
Qed.

Lemma wfr_VAL_set_sub_region rmap m0 s1 s2 xn pk sr p ws w mem2 :
  let: x := {| vtype := sword ws; vname := xn |} in
  valid_state rmap m0 s1 s2 ->
  get_local pmap x = Some pk ->
  wf_sub_region sr x.(vtype) ->
  valid_pk rmap s2 sr pk ->
  ~ Sv.In x pmap.(vnew) ->
  between (sub_region_addr sr) (size_slot x) p ws ->
  write_mem (emem s2) p ws w = ok mem2 ->
  wfr_VAL rmap s1 s2 ->
  wfr_VAL (set_sub_region rmap x sr) (with_vm s1 (evm s1).[x <- ok (pword_of_word w)]) (with_mem s2 mem2).
Proof.
  move=> hvs hget hwf hpk hnin hb hw hwfr y sry bytes vy. (* hvalid. *)
  move=> /check_gvalid_set_sub_region [|[]].
  move=> [hd hcv]; rewrite get_gvar_neq // => /hwfr -/(_ _ _ hcv) /=.
  apply: (eq_mp_val_write_disj hvs hwf) hw.
  Search _ (~ is_glob _ -> _). (*
  intros.
  
   admit.
  move: y => [[yv yi] yn] => /=. move=> [?? ??]. subst yv=> /=.
  rewrite (@get_gvar_eq _ {| gv := {| v_var := {| vtype := sword ws; vname := xn |}; v_info := yi |}; gs := yn |}).
  simpl. move=> [<-]. exists w. split=> //.
  intros. subst sry.
  move: hb; rewrite /between /zbetween !zify /=.
  move=> [??].
  assert (wunsigned (sub_region_addr sr) = wunsigned p) by lia.
  Search _ wunsigned. apply wunsigned_inj in H0. rewrite H0.
          apply: Memory.writeP_eq hw. done.
  
  rewrite /check_gvalid.
  case: (@idP (is_glob y)) => hg.
  case heq: Mvar.get => [[ofs ws']|//] [<- <-].
  case hty: y.(gv).(vtype) => //= [n|ws'].
  Search _ get_var.
  Search get_gvar stype.
  apply: on_arr_gvarP. => n t hty /= hget.
  + move=> hg. rewrite /eq_sub_region_array.
  Search _ get_gvar vtype.
  rewrite /check_gvalid in hvalid.
  case: (is_glob y) hvalid. admit.
  case hget2: Mvar.get=> // -[-> <-].
  rewrite /= in hget2. rewrite Mvar.setP in hget2.
  move: hget2. case: eqP. admit.
  move=> ? hget2.
  get_gvar
  on_arr_gvarP
   move=> /=.
  rewrite Mvar.setP; case: eqP.
  + move=> <- [<-].
    exists pk; split=> //.
    by apply (valid_pk_set_sub_region hvs hwf hnin hb hw (wf_locals hget) hpk).
  move=> _ /hwfr {pk hget hpk} [pk [hget hpk]].
  exists pk; split=> //.
  by apply (valid_pk_set_sub_region hvs hwf hnin hb hw (wf_locals hget) hpk).
Qed.*)
Abort.

(*
Lemma eq_glob_rset_word rmap m0 s1 s2 x mp p ws w mem2:
  valid_state rmap m0 s1 s2 ->  
  Mvar.get (var_region rmap) x = Some mp ->
  mp_s mp = MSstack ->
  between (mp_addr mp) (size_of (vtype x)) p ws ->
  write_mem (emem s2) p ws w = ok mem2 ->
  eq_glob (emem s1) (emem s2) ->
  eq_glob (emem s1) mem2.
Proof.
  move=> hvs hgx hms hb hw heg p1 ws1 hvp.
  rewrite (heg _ _ hvp); symmetry; apply: (Memory.writeP_neq hw).
  assert (hd:= vs_disj (ms:= mp_s mp) hvp); move:hd; rewrite hms /wptr /wptr_size /= => hd.
  assert (hmp := wfr_valid_mp hgx).
  case: (hmp) => x' [] /size_of_le hle; rewrite hms /= => hx.
  split.
  + by apply (is_align_no_overflow (Memory.valid_align (write_mem_valid_pointer hw))).
  + by apply: is_align_no_overflow (Memory.valid_align hvp).
  move: hb; rewrite /between !zify.
  assert (hwl := wfg_ofs wf_locals (get_local_pos hx)).
  rewrite (valid_mp_addr hmp) /wptr hms /=; lia.
Qed.

Lemma eq_not_mod_rset_word rmap m0 s1 s2 x mp p ws w mem2:
  valid_state rmap m0 s1 s2 ->  
  Mvar.get (var_region rmap) x = Some mp ->
  mp_s mp = MSstack ->
  between (mp_addr mp) (size_of (vtype x)) p ws ->
  write_mem (emem s2) p ws w = ok mem2 ->
  eq_not_mod m0 (emem s2) -> 
  eq_not_mod m0 mem2. 
Proof.
  move=> hvs hgx hms hb hw heg p1 ws1 hvp.
  rewrite (heg _ _ hvp) //; symmetry; apply: (Memory.writeP_neq hw).
  assert (hmp := wfr_valid_mp hgx).
  case: (hmp) => x' [] /size_of_le hle; rewrite hms /= => hx.
  split.
  + by apply (is_align_no_overflow (Memory.valid_align (write_mem_valid_pointer hw))).
  + by apply: is_align_no_overflow; apply is_align8.
  move: hb; rewrite /between !zify.
  have:= hvp _ _ _ (get_local_pos hx).
  rewrite wunsigned_add; last by have := @ge0_wunsigned _ rsp; lia.
  rewrite (valid_mp_addr hmp) /wptr hms wsize8 /=; lia.
Qed.
*)

Lemma set_word_align rmap m0 s1 s2 x sr ws rmap' :
  valid_state rmap m0 s1 s2 ->
  wf_sub_region sr x.(vtype) ->
  set_word rmap x sr ws = ok rmap' ->
  [/\ is_align (sub_region_addr sr) ws
    & sr.(sr_region).(r_writable)].
Proof.
  by rewrite /set_word; t_xrbindP=> hvalid hwf _ /assertP -> _ /(check_alignP hvalid hwf).
Qed.

Lemma set_sub_region_wf rmap x sr :
  wf_sub_region sr x.(vtype) ->
  wf_var_region rmap ->
  wf_var_region (set_sub_region rmap x sr).
Proof.
  move=> hwf hwf2.
  rewrite /set_sub_region /wf_var_region /= => y sr'.
  by rewrite Mvar.setP; case: eqP; [congruence|auto].
Qed.

Lemma test sr ofs :
  wunsigned (sub_region_addr sr + wrepr _ ofs) =
  wunsigned (sub_region_addr (sub_region_at_ofs sr (Some ofs) (wsize_size U8))).
Proof.
  rewrite /sub_region_addr /=. rewrite wrepr_add GRing.addrA. reflexivity.
Qed.

(* Ceci est un test *)
Definition clear_sub_region (rmap : region_map) sr :=
  let z := sr_zone sr in
  let i := interval_of_zone z in
  let bm := get_bytes_map (sr_region sr) rmap in
  let bm := clear_bytes_map i bm in
  {| var_region := rmap.(var_region);
     region_var := Mr.set rmap.(region_var) (sr_region sr) bm
  |}.

(* TODO: factorize set_sub_region and similar *)
Lemma get_var_bytes_clear_sub_region rmap sr r y :
  get_var_bytes (clear_sub_region rmap sr) r y =
    if sr.(sr_region) != r then
      get_var_bytes rmap r y
    else
      let i := interval_of_zone sr.(sr_zone) in
      let bytes := get_var_bytes rmap r y in
      ByteSet.remove bytes i.
Proof.
  rewrite /clear_sub_region /get_var_bytes /=.
  rewrite get_bytes_map_setP.
  case: eqP => [->|heq] //=.
  by rewrite get_bytes_clear.
Qed.

Lemma check_gvalid_clear_sub_region rmap sr y sry bytes :
  check_gvalid (clear_sub_region rmap sr) y = Some (sry, bytes) ->
    [/\ is_glob y & check_gvalid rmap y = Some (sry, bytes)] \/
(*    [/\ ~ is_glob y, x <> gv y, Mvar.get rmap.(var_region) y.(gv) = Some sry &
        bytes = get_var_bytes (set_sub_region rmap x sr) sry.(sr_region) y.(gv)] \/ *)
    [/\ ~ is_glob y (* x = gv y, sr = sry *)&
        bytes = (* ByteSet.remove (get_var_bytes rmap sry.(sr_region) y.(gv)) (interval_of_zone sr.(sr_zone))]. *)
        get_var_bytes (clear_sub_region rmap sr) sry.(sr_region) y.(gv)].
Proof.
  rewrite /check_gvalid.
  case: (@idP (is_glob y)) => hg.
  + by case heq: Mvar.get => [[ofs ws]|//] [<- <-]; left; split.
  case heq: Mvar.get=> //.
  + move=> [-> <-].
    by right; split.
Qed.

Lemma lemme_benjamin rmap ty sr p ws w s s' y sry rmap' (* p' *) ws' srz bytes :
  wf_sub_region sr ty ->
  clear_sub_region rmap sr = rmap' ->
  write_mem s p ws w = ok s' ->
  between (sub_region_addr sr) (size_of ty) p ws ->
  check_gvalid rmap' y = Some (sry, bytes) ->
  wf_sub_region srz (sword ws') ->
  ByteSet.mem bytes (interval_of_zone srz.(sr_zone)) ->
(*   between (sub_region_addr sry) (size_slot y) p' ws' -> *)
  read_mem s (sub_region_addr srz) ws' = read_mem s' (sub_region_addr srz) ws'.
Proof.
  move=> hwf <- hw hb /check_gvalid_clear_sub_region [].
  + move=> [hg hvalid] hwf' hmem. symmetry. apply (Memory.writeP_neq hw).
    admit.
  move=> [hloc ->] hwf'.
  rewrite get_var_bytes_clear_sub_region.
  case: eqP => /=.
  symmetry. apply (Memory.writeP_neq hw).
  apply mem_remove in H. (* ...*) admit.
  symmetry. apply (Memory.writeP_neq hw).
  (* different regions : disjoint -> one must probably be writable *)
Abort.

(* TODO : disjoint_intervals (interval_of_zone _ ) = disjoint_zones z1 z2
          et disjoint_zones -> disjoint_zrange avec même base *)
Lemma alloc_lvalP rmap r1 r2 v ty m0 (s1 s2: estate) :
  alloc_lval pmap rmap r1 ty = ok r2 -> 
  valid_state rmap m0 s1 s2 -> 
  type_of_val v = ty ->
  forall s1', write_lval gd r1 v s1 = ok s1' ->
  exists s2', write_lval [::] r2.2 v s2 = ok s2' /\ valid_state r2.1 m0 s1' s2'.
Proof.
  move=> ha hvs ?; subst ty.
  case: r1 ha => /=.
  (* Lnone *)
  + move=> vi ty1 [<-] /= s1' /write_noneP [->] h; exists s2; split => //.
    by rewrite /write_none; case: h => [ [? ->]| [-> ->]].

  (* Lvar *)
  + move=> x; t_xrbindP => _ /check_diffP hnnew.
    case hlx: get_local => [pk | ]; last first.
    + move=> [<-] s1'.
      rewrite /write_var; t_xrbindP => vm1 hvm1 <- /=.
      by apply: set_varP hvm1=> [v' hv <- | hb hv <-]; rewrite /write_var /set_var hv /= ?hb /=;
        eexists;(split;first by reflexivity); apply valid_state_set_var.
    case heq: is_word_type => [ws | //]; move /is_word_typeP : heq => hty.
    case: eqP => htyv //; rewrite /write_var.
    t_xrbindP => -[xi ei] ha sr hsr rmap2 hsetw <- /= s1' vm1' hvm1' ?; subst s1' => /=.
    have he1 : sem_pexpr [::] s2 0 >>= to_int = ok 0 by done.
    have hpk := sub_region_pk_valid rmap s2 hsr.
    have [wx [wi [-> -> /= <-]]]:= check_mk_addr_ptr hvs he1 hlx hpk ha.
    move: hvm1'; apply set_varP; last by rewrite {1}hty.
    move=> {ha}; case: x hty hlx hsetw hnnew => -[xty xn] xii /= ->.
    set x := {| vtype := sword ws; vname := xn |} => hlx hsetw hnnew /= w.
    move=> /(type_of_val_to_pword htyv) [w' [??]] ?; subst v vm1' => /=.
    rewrite truncate_word_u /= wrepr0 GRing.addr0.
    have hwf := sub_region_pk_wf hlx refl_equal hsr.
    have hvp: valid_pointer (emem s2) (sub_region_addr sr) ws.
    + have [halign _] := set_word_align hvs hwf hsetw.
      apply /Memory.valid_pointerP; split=> //.
      move=> k hk.
      have hal: is_align (sub_region_addr sr + wrepr U64 (k * mk_scale AAdirect U8)) U8.
      + by apply is_align8.
      have /= := wf_sub_region_valid_pointer hvs hwf hal.
      by rewrite Z.mul_1_r wsize8; apply; lia.
    have /Memory.writeV -/(_ w') [mem2 hmem2] := hvp.
    rewrite hmem2 /=; eexists;split;first by reflexivity.
    (* valid_state update word *)
    case:(hvs) => hvalid hdisj hincl hunch hrip hrsp hwfr heqvm hwfr2 heqmem.
(*    have hbet: between (sub_region_addr sr) (size_of (vtype x)) (mp_addr mp) ws.
    + by rewrite /between /x /= !Z.leb_refl. *)
    constructor => //=.
    + by move=> ??; rewrite (Memory.write_valid _ _ hmem2); apply hvalid.
    + by move=> ??; rewrite (Memory.write_valid _ _ hmem2); apply hincl.
    + move=> p ws' hvalid2 hvalid3 hdisj2.
      rewrite (hunch p ws' hvalid2 hvalid3 hdisj2).
      symmetry; apply (Memory.writeP_neq hmem2).
      have [_ hwritable] := set_word_align hvs hwf hsetw.
      have := hdisj2 _ hwf.(wfr_slot).
      rewrite hwf.(wfr_writable)=> /(_ hwritable).
      apply: disjoint_zrange_incl_l.
      apply (zbetween_sub_region_addr hwf).
    + move: hsetw; rewrite /set_word; t_xrbindP => _ _ _ _ <-.
      by apply: set_sub_region_wf hwfr.
    + move=> y hget; rewrite get_var_neq; first by apply heqvm.
      by rewrite /get_local in hlx; congruence.
    + split; last first.
      + move: hsetw; rewrite /set_word; t_xrbindP => _ /assertP hwritable _ _ <-.
        apply (wfr_PTR_set_sub_region hvs hlx hwf hpk hnnew (zbetween_refl _ _) hmem2).
        by apply hwfr2.
      
      
      move=> y sry.
        move: hsetw; rewrite /set_word; t_xrbindP => _ /assertP hwritable _ _ <-. (* /=. *)
        move=> bytes v /check_gvalid_set_sub_region [|[]].
        move=> [] hg hcheck. rewrite get_gvar_neq => // hgvar.
        assert (H := wfr_val hcheck hgvar); move: H.
        
        apply: disjoint_zrange_eq_sub_region_val hmem2. apply (check_gvalid_wf hvs hcheck).
        apply (disjoint_zrange_incl_l (zbetween_sub_region_addr hwf)).
        apply (disjoint_zrange_incl_r (zbetween_sub_region_addr (check_gvalid_wf hvs hcheck))).
        apply: disjoint_writable.
        apply hwf.(wfr_slot).
        apply (check_gvalid_wf hvs hcheck).(wfr_slot). admit.
        rewrite hwf.(wfr_writable) => //.
        move=> [] hl hneq hcheck hb.
        rewrite get_gvar_neq => // hgvar.
        move: hb.
        rewrite get_var_bytes_set_sub_region.
        case: eqP => /=.
        case: eqP => // _.
        have : check_gvalid rmap y = Some (sry, get_var_bytes rmap sry.(sr_region) y.(gv)).
        + rewrite /check_gvalid. case: (@idP (is_glob y)) => // _.
        rewrite hcheck. reflexivity.
        move => /wfr_val /(_ hgvar).
        move=> h1 h2 h3. move: h1.
        case heq3: (vtype (gv y)) => // [pt | ws']; rewrite /size_of => /=.
  + move=> [t] [-> heq]; exists t; split => // off hoff hmem v1.
  subst bytes. rewrite ByteSet.removeE in hmem.
  move: hmem.
  move=> /andP [] hmem hnot /(heq _ hoff hmem) <-.
    apply: (Memory.writeP_neq hmem2).
    rewrite /disjoint_range /disjoint_zrange /no_overflow.
    rewrite test -!/(no_overflow _ _) -/(disjoint_zrange _ _ _ _).
    change (wsize_size U8) with (size_of sword8).
    apply (disjoint_zones_disjoint_zrange hwf).
    Search _ sub_region_at_ofs wf_sub_region.
    apply (wf_sub_region_sub_zone (vs_wf_region hcheck) (ofs := Some off)).
    move=> _ [<-]. rewrite heq3 wsize8 /=. lia. assumption.
    rewrite /=.
    rewrite /disjoint_zones !Zcmp_le !zify /=.
    rewrite /I.memi /= in hnot.
    move /negP : hnot. rewrite !zify.
    rewrite wsize8. lia.
    
    move=> [w1] [-> heq]; exists w1; split => //.
    subst bytes. move=> /mem_remove [hmem hnot]. rewrite -(heq hmem).
    apply: (Memory.writeP_neq hmem2).
    assert (hwf' := vs_wf_region hcheck).
    rewrite heq3 in hwf'.
    apply (disjoint_zones_disjoint_zrange hwf hwf').
    assumption.
    rewrite -/(interval_of_zone {| z_ofs := z_ofs (sr_zone sry); z_len := wsize_size ws' |}) in hnot.
    rewrite disjoint_interval_of_zone in hnot.
    have hofs := hwf'.(wfz_ofs).
    (* unprovable ! on a le même problème qu'avec les stkptr :
       - d'un côté on utilise la longueur de la zone z_len
       - de l'autre on utilise la longueur du type du slot
       - on sait que size_slot slot <= z_len mais pas le contraire !
       il faut changer disjoint_zones_disjoint_zrange ?
    *)
    
    
    ; rewrite -(heq hmem).
  by apply: (Memory.writeP_neq hw).
    
    
    apply 
    pose :=(disjoint_range (sub_region_addr sr) ws (sub_region_addr (sub_region_at_ofs sry (Some off) (wsize_size U8))) U8).
    move: eaz.
    rewrite /disjoint_range /disjoint_zrange in eaz.
    sub_zone_at_ofs
    move: hnot => /negP; rewrite /I.memi !zify /interval_of_zone /= => hnot.
    apply: disjoint_zrange_byte.
    rewrite /disjoint_range /disjoint_zrange. split.
    apply (no_overflow_sub_region_addr hwf).
    apply: no_overflow_incl.
    2: apply (no_overflow_sub_region_addr (vs_wf_region hcheck)).
    apply: zbetween_byte. apply (no_overflow_sub_region_addr (vs_wf_region hcheck)).
    apply zbetween_refl. rewrite heq3.
    assumption.
    admit.
    rewrite (wunsigned_sub_region_addr hwf).
    rewrite wunsigned_add /sub_region_addr.
    rewrite !wunsigned_add. rewrite h2.
    assert (z_ofs (sr_zone sr) > z_ofs (sr_zone sry) + off
          \/ z_ofs (sr_zone sry) + off >= z_ofs (sr_zone sr) + z_len (sr_zone sr)) by lia.
    destruct H.  right. rewrite wsize8.
    lia.
    left. have hlen := hwf.(wfz_len). rewrite /x /= in hlen. lia.
    addr_no_overflow
    
     lia. 2:admit.
    
    move /negP in hnot. rewrite /I.memi in hnot. rewrite zify in hnot.
    apply: disjoint_zrange_incl_r.
    apply: zbetween_byte.
    apply no_overflow_sub_region_addr. apply (vs_wf_region hcheck). apply zbetween_refl.
    rewrite heq3. assumption.
    change (wsize_size ws) with (size_of (sword ws)).
    apply disjoint_zones_disjoint_zrange. assumption.
    apply (vs_wf_region hcheck). assumption.
    by apply zbetween_refl.
  move=> [w1] [-> heq]; exists w1; split => // hmem; rewrite -(heq hmem).
  by apply: (Memory.writeP_neq hw).
Qed.
        case: (vtype (gv y)) => //= [ws'|ws'].
        move=> [p] [->].
        apply: disjoint_zrange_eq_sub_region_val hmem2. apply (check_gvalid_wf hvs hcheck).
        apply (disjoint_zrange_incl_l (zbetween_sub_region_addr hwf)).
        apply (disjoint_zrange_incl_r (zbetween_sub_region_addr (check_gvalid_wf hvs hcheck))).
        apply: disjoint_writable.
        apply hwf.(wfr_slot).
        apply (check_gvalid_wf hvs hcheck).(wfr_slot). admit.
        rewrite hwf.(wfr_writable) => //. *) admit.
        move=> [] hl heq heq' hb. subst sry.
        rewrite /=.
        case: y hl heq => [[yv yi] yn] /= hg ?. subst yv.
        
         rewrite /=.
         rewrite (@get_gvar_eq gd {| gv := {| v_var := x; v_info := yi |}; gs := yn |}) //=.
         move=> [<-]; exists w';split;first by subst w.
         move=> _.
         by apply: Memory.writeP_eq hmem2.
         move=> ?.
         apply wfr_val.
         Search _ word pword.
         exists (word_ofpword w). exists (Vword (pw_word w)). eq_sub_region_word exists (pw_word w). constructor.

        
        
        
        rewrite Mvar.setP; case: eqP.
        + move=> <- [<-]; exists pk; split=> //. apply sub_region_pk_valid.
        move=> _ hget.
        case: (wfr_ptr hget) => pk' [hlocal hpk'].
        exists pk'; split=> //.
        case: pk' hlocal hpk'=> //; rewrite /valid_pk /=.
        move=> s ofs ws' z f hget2 hcheck.
        case: (sr.(sr_region).(r_slot) =P s); last first.
        + move=> hneq; rewrite (check_stack_ptr_neq _ _ _ _ _ hneq) => /hcheck <-.
          apply (Memory.writeP_neq hmem2).
          assert (hdisj2 := disjoint_writable (hwf.(wfr_slot)) (wf_locals hget2).(wfs_slot) hneq).
          (* TODO : disjoint_zrange_incl specialized to sub_region_addr *)
          (* or prove incl (sub_region_addr ) (Addr _) (size_slot ...) *)
          rewrite hwf.(wfr_writable) in hdisj2; apply: disjoint_zrange_incl (hdisj2 hwritable).
          + by apply (sub_region_addr_zbetween hwf).
          by apply (sub_region_addr_zbetween (get_local_stkptr_wf hget2)).
        move=> ?; subst s.
        rewrite /check_stack_ptr.
        have := get_set_sub_region rmap x sr {| r_slot := r_slot (sr_region sr); r_align := ws'; r_writable := true |} f.
        rewrite /get_bytes' /= => ->.
        case: ifP => [|_].
        + move=> /eqP [].
          have [[] _] := hwf.
          case: (wf_locals hget2).
          by case: sr.(sr_region) => /=; congruence.
        case: eqP => [|_].
        + by assert (hnew := (wf_locals hget2).(wfs_new)); congruence.
        t_xrbindP=> _ /assertP hmem _.
        rewrite -hcheck.
        + apply (Memory.writeP_neq hmem2).
        apply mem_remove in hmem.
        case: hmem.
          rewrite (disjoint_interval_of_zone (wf_zone_len_gt0 hwf)
          (z2 := {| z_ofs := z_ofs z; z_len := wsize_size U64 |})
           ltac:(rewrite /wsize_size /=; lia)) => hmem hdisj2.
        apply test2. assumption. apply (get_local_stkptr_wf hget2).
        rewrite /=.
        (* on prouve la même chose 2 x : factoriser les 3 lignes suivantes *)
        have [[] _] := hwf.
        case: (wf_locals hget2).
        by case: sr.(sr_region) => /=; congruence. rewrite /=.
        case: hmem => hmem /disjoint_intervalsP.
        rewrite /interval_of_zone /I.is_empty !zify /= {1}/wsize_size => hdisj2.
        rewrite /disjoint_range /disjoint_zrange.
        split.
        + have := addr_no_overflow hwf.(wfr_slot).
          have hofs := wfsr_sub hwf.
          have hsize := wfss_size hwf.
          rewrite /no_overflow !zify (slot_wunsigned_addr hwf).
          by rewrite /x /= in hsize; lia.
        + have /= hwf2 := get_local_stkptr_wf hget2.
          have /= := addr_no_overflow hwf2.(wfr_slot).
          have /= hofs := wfsr_sub hwf2.
          have /= hsize := wfss_size hwf2.
          rewrite /no_overflow !zify (slot_wunsigned_addr hwf2) /=.
          by lia.
        rewrite (slot_wunsigned_addr hwf).
        rewrite (slot_wunsigned_addr (get_local_stkptr_wf hget2)) /=.
        have hofs := wfsr_sub hwf.
        have hsize := wfss_size hwf.
        have hlen := wfsr_len hwf.
        rewrite /x /= in hsize. right. lia.
      by rewrite /check_stack_ptr (proj1 (mem_remove hmem)).
    rewrite /wfr_VAL.
    move=> x' sr' bytes v.
    case hty: x'.(gv).(vtype) => /=.
    have [hval _] := hwfr2.
    rewrite /wfr_VAL in hval.
           specialize (hdisj2 hwritable).
          
          
      have [_ hwritable] := set_word_align hvs hwf hsetw.
      have := hdisj2 _ hwf.(wfr_slot).
      rewrite hwf.(wfr_writable)=> /(_ hwritable).
      apply: disjoint_zrange_incl.
      rewrite (slot_wunsigned_addr hwf).
      have hofs := wfsr_sub hwf.
      have hsize := wfss_size hwf.
      by rewrite /x /size_slot /= in hsize; lia.
        valid_pk
        wfr_VAL
        apply hwfr2.
    + by rewrite -(ss_frames (Memory.write_mem_stable hmem2)).
    + move=> y hy; rewrite get_var_neq; first by apply heqvm.
      by move=> heq;move: hy; rewrite -heq hlx.
    + (* TODO : faire un lemme à part sur set_sub_region et sub_region_pk ? *)
      (* ça réduirait la taille de la preuve, mais le lemme serait juste "technique" *)
      case: (hwfr) => h1 h2 h3; constructor => //=.
      + move=> y mpy v /(check_gvalid_rset_word hins hgetr) [].
        + move=> [ hng heq ?]; subst mpy.
          have -> : y = mk_lvar {|v_var := x; v_info := v_info (gv y) |}.
          + by case: y hng heq => -[yv vi] [] //= _ ->.
          have /= -> // := @get_gvar_eq gd (mk_lvar {| v_var := x; v_info := v_info (gv y) |}) (evm s1) (ok w).
          move=> [<-]; exists w';split;first by subst w.
          by apply: Memory.writeP_eq hmem2.
        move=> [hd hdm hcv]; rewrite get_gvar_neq // => /h2 -/(_ _ hcv) /=.
        by apply: (eq_mp_val_write_disj hvs hgetr) hmem2.
      by apply: wfr_PTR_rset_word hmem2 h3.
    + by apply: (eq_glob_rset_word hvs hgetr) hmem2 heqg.
    by apply: (eq_not_mod_rset_word hvs hgetr) hmem2 hnotm.

  (* Lmem *)
  + move=> ws x e1; t_xrbindP => ? /check_varP hx e1' /(alloc_eP hvs) he1 <-.
    move=> s1' xp ? hgx hxp w1 v1 /he1 he1' hv1 w hvw mem2 hw <- /=.
    have := get_var_kindP hvs hx; rewrite /get_gvar /= => /(_ _ hgx) -> /=.
    rewrite he1' hxp /= hv1 /= hvw /=.
    have hvp1 := write_mem_valid_pointer hw.
    have hvp2: valid_pointer (emem s2) (xp + w1) ws.
    + by apply /Memory.readV; assert (h := vs_eq_mem hvp1); rewrite -h; apply /Memory.readV.
    have /Memory.writeV  -/(_ w) [mem2' hmem2] := hvp2.
    rewrite hmem2 /=; eexists;split;first reflexivity.
    (* valid_state update mem *)
    case:(hvs) => vptr hdisj hrip hrsp hf heqvm hwfr heqg hnotm. 
    have ha1 := Memory.valid_align hvp1.
    have hno1 := is_align_no_overflow ha1.
    constructor => //=.
    + by move=> ???; rewrite (Memory.write_valid _ _ hmem2); apply vptr.
    + by move=> ??; rewrite (Memory.write_valid _ _ hw); apply hdisj.
    + by rewrite -(ss_frames (Memory.write_mem_stable hmem2)).
    + case: (hwfr) => h1 h2 h3; constructor => //=.
      + move=> y mpy vy hcv hgy.
        have hmp := check_gvalid_mp hvs hcv.
        apply: (disjoint_eq_mp_val hmp _ hmem2 (h2 _ _ _ hcv hgy)).
        have hb1 := valid_mp_addr_bound hmp; have hb2 := @ms_bound (mp_s mpy).
        split => //.
        + by rewrite /no_overflow !zify; lia.
        by have:= hdisj _ _ (mp_s mpy) hvp1; lia.
      move=> y mpy hgy.
      have [pk [hgpk hvpk]] := h3 _ _ hgy; exists pk; split => //.
      case: pk hgpk hvpk => //= ofs /get_local_pos_sptr hgpk <-.
      apply: (Memory.writeP_neq hmem2).
      have h := sptr_addr_bound hgpk; split => //.
      + rewrite /no_overflow !zify; lia.
      by have:= hdisj _ _ MSstack hvp1; rewrite /wptr /wptr_size /=; lia.
    + move=> w2 sz; rewrite (Memory.write_valid _ _ hw) => hv.
      by apply: Memory.read_write_any_mem (hw) (hmem2) => //; apply heqg.
    move=> ofs hofs hl; rewrite hnotm //.
    symmetry; apply: (Memory.writeP_neq hmem2).
    split => //.
    + by rewrite /no_overflow zify wsize8; have := wunsigned_range (rsp + wrepr U64 ofs); lia.
    rewrite wsize8 wunsigned_add; last by have := @ge0_wunsigned _ rsp; lia.
    by have:= hdisj _ _ MSstack hvp1; rewrite /wptr /wptr_size /=; lia.
  
  (* Laset *)
  move=> aa ws x e1; t_xrbindP => e1' /(alloc_eP hvs) he1.
  move=> hr2 s1'; apply on_arr_varP => n t hty hxt.
  t_xrbindP => i1 v1 /he1 he1' hi1 w hvw t' htt' vm1 hvm1 ?; subst s1'.
  case hlx: get_local hr2 => [pk | ]; last first.
  + t_xrbindP => ? /check_diffP hnnew <-.
    have /get_var_kindP -/(_ _ hxt) : get_var_kind pmap (mk_lvar x) = ok None.
    + by rewrite /get_var_kind /= hlx.
    rewrite /get_gvar /= => hxt2.
    rewrite he1' /= hi1 hxt2 /= hvw /= htt' /=.
    apply: set_varP hvm1=> [v' hv <- | ]; last by rewrite {1} hty.
    rewrite /set_var hv /=.
    by eexists;(split;first by reflexivity); apply valid_state_set_var. 
  t_xrbindP => mp hc -[xi ei] ha rmap2 hsetw <- /=.
  have {he1} he1 : sem_pexpr [::] s2 e1' >>= to_int = ok i1 by rewrite he1'.
  have [mp' [hgetr hins hal ->]] := set_wordP hsetw. 
  have ? : mp = mp'.
  + by move /check_validP : hc; rewrite hgetr => -[[->]].
  subst mp'.
  have [wx [wi [-> -> /= <- hmpal]]]:= check_mk_addr_ptr hvs he1 hlx hgetr hal ha.
  move: hvm1; apply set_varP; last by rewrite {1}hty.
  move=> {ha hsetw}; case: x hty hlx hxt hc hgetr => -[xty xn] xii /= ->.
  set x := {| vtype := sarr n; vname := xn |} => hlx hxt hc hgetr /= ti [?] ?; subst ti vm1.
  rewrite hvw /=.
  have [hge0 hlen haa] := WArray.set_bound htt'.
  assert (hmp := wfr_valid_mp hgetr).
  have ha := valid_mp_addr hmp; have /= hab:= valid_mp_addr_bound hmp.
  have /= hmpb := valid_mp_bound hmp; have hmsb:= @ms_bound (mp_s mp).
  have hvp: valid_pointer (emem s2) (mp_addr mp + wrepr Uptr (i1 * mk_scale aa ws)) ws.
  + apply Memory.is_align_valid_pointer. 
    + by apply is_align_add => //; apply arr_is_align. 
    move=> k hk; rewrite /mp_addr -!GRing.addrA -!wrepr_add.
    apply vs_val_ptr; split; first by apply ge0_wunsigned.
    by apply: Z.le_lt_trans; first apply wunsigned_repr_le; lia.
  have /Memory.writeV -/(_ w) [mem2 hmem2] := hvp.
  rewrite hmem2 /=; eexists;split;first by reflexivity.
  (* valid_state update array *)
  have hgt0ws := wsize_size_pos ws; have ge0_mps := @ge0_wunsigned _ (wptr (mp_s mp)).
  have heqa : wunsigned (mp_addr mp + wrepr U64 (i1 * mk_scale aa ws)) = 
              wunsigned (mp_addr mp) + i1 * mk_scale aa ws.
  + by apply wunsigned_add; lia.
  case:(hvs) => vptr hdisj hrip hrsp hf heqvm hwfr heqg hnotm. 
  have hbet: between (mp_addr mp) (size_of (vtype x)) (mp_addr mp + wrepr U64 (i1 * mk_scale aa ws)) ws.
  + by rewrite /between /x /= !zify; lia.
  constructor => //=.
  + by move=> ???; rewrite (Memory.write_valid _ _ hmem2); apply vptr.
  + by rewrite -(ss_frames (Memory.write_mem_stable hmem2)).
  + move=> y hy; rewrite get_var_neq; first by apply heqvm.
    by move=> heq;move: hy; rewrite -heq hlx.
  + case: (hwfr) => h1 h2 h3; constructor => //=.
    + move=> y mpy vy /(check_gvalid_rset_word hins hgetr) [].
      + move=> [ hng heq ?]; subst mpy.
        have -> : y = mk_lvar {|v_var := x; v_info := v_info (gv y) |}.
        + by case: y hng heq => -[yv vi] [] //= _ ->.
        set X := (mk_lvar {| v_var := x; v_info := v_info (gv y) |}).
        have /= -> // := @get_gvar_eq gd X (evm s1) (ok (WArray.inject n t')).
        move=> [<-]; eexists (WArray.inject n t');split => //.
        move=> off hoff v0.
        have -> :  WArray.get AAscale U8 (WArray.inject n t') off = WArray.get AAscale U8 t' off.
        + by rewrite /WArray.inject Z.ltb_irrefl.
        rewrite Z.add_comm wrepr_add GRing.addrA -/(mp_addr mp) (WArray.set_get8 off htt') /=.
        have -> /= := Memory.write_read8 (mp_addr mp + wrepr U64 off) hmem2.
        set t1 := (x in (if x then _ else _)).
        set t2 := (x in _ -> (if x then _ else _) = _).
        have <- : t1 = t2.
        + rewrite Bool.eq_iff_eq_true -/(is_true t1) -/(is_true t2) /t1 /t2 !zify.
          by rewrite !(@wunsigned_add _ (mp_addr mp)); lia.
        case:ifPn; rewrite /t1 !zify => hi {t1 t2}.
        + move=> [<-]; do 2 f_equal; rewrite !(@wunsigned_add _ (mp_addr mp)); lia.
        move=> hh; have hcg : check_gvalid rmap X = Some mp.
        + by rewrite /check_gvalid /= hc.
        have /= [t1 [/Varr_inj]]:= h2 _ _ _ hcg hxt.
        move=> [heq1]; rewrite (Eqdep_dec.UIP_dec Pos.eq_dec heq1 erefl) /= => ?; subst t1 => {heq1}.
        by move=> /(_ _ hoff _ hh) <-; rewrite Z.add_comm wrepr_add GRing.addrA -/(mp_addr mp).
      move=> [hd hdm hcv]; rewrite get_gvar_neq // => /h2 -/(_ _ hcv) /=.
      by apply: (eq_mp_val_write_disj hvs hgetr) hmem2.
    by apply: wfr_PTR_rset_word hmem2 h3.
  + by apply: (eq_glob_rset_word hvs hgetr) hmem2 heqg.
  by apply: (eq_not_mod_rset_word hvs hgetr) hmem2 hnotm.
Qed.

Lemma alloc_lvalsP rmap r1 r2 vs ty m0 (s1 s2: estate) :
  alloc_lvals pmap rmap r1 ty = ok r2 -> 
  valid_state rmap m0 s1 s2 -> 
  seq.map type_of_val vs = ty -> 
  forall s1', write_lvals gd s1 r1 vs = ok s1' ->
  exists s2', write_lvals [::] s2 r2.2 vs = ok s2' /\ valid_state r2.1 m0 s1' s2'.
Proof.
  elim: r1 r2 rmap ty vs s1 s2=> //= [|a l IH] r2 rmap [ | ty tys] // [ | v vs] //.
  + move=> s1 s2 [<-] Hvalid _ s1' [] <-; by exists s2; split.
  move=> vs's1 s2; t_xrbindP => -[a' r3] ha [l' r4] /IH hrec <-.
  move=> Hvalid [] hty htys s1' s1'' ha1 hl1.
  have [s2' [hs2' vs2']]:= alloc_lvalP ha Hvalid hty ha1.
  have [s2'' [hs2'' vs2'']]:= hrec _ _ _ vs2' htys _ hl1.
  by exists s2''; split => //=; rewrite hs2'.
Qed.



(*Hypothesis P

Let P' : sprog := 
    {| p_globs := [::];
       p_funcs := SP;
       p_extra := {|
         sp_rip := gm.(stack_alloc.rip); 
         sp_globs := data; 
         sp_stk_id := nrsp |}
    |}. *)

Variable (P' : sprog).
Hypothesis P'_globs : P'.(p_globs) = [::].
Variable (m0:mem).

Let Pi_r s1 (i1:instr_r) s2 :=
  forall rmap1 rmap2 ii1 ii2 i2, alloc_i pmap rmap1 (MkI ii1 i1) = ok (rmap2, MkI ii2 i2) ->
  forall s1', valid_state rmap1 m0 s1 s1' ->
  exists s2', sem_i (sCP:= sCP_stack) P' rip s1' i2 s2' /\ valid_state rmap2 m0 s2 s2'.

Let Pi s1 (i1:instr) s2 :=
  forall rmap1 rmap2 i2, alloc_i pmap rmap1 i1 = ok (rmap2, i2) ->
  forall s1', valid_state rmap1 m0 s1 s1' ->
  exists s2', sem_I (sCP:= sCP_stack) P' rip s1' i2 s2' /\ valid_state rmap2 m0 s2 s2'.

Let Pc s1 (c1:cmd) s2 :=
  forall rmap1 rmap2 c2,  fmapM (alloc_i pmap) rmap1 c1 = ok (rmap2, c2) ->
  forall s1', valid_state rmap1 m0 s1 s1' ->
  exists s2', sem (sCP:= sCP_stack) P' rip s1' c2 s2' /\ valid_state rmap2 m0 s2 s2'.

Let Pfor (i1: var_i) (vs: seq Z) (s1: estate) (c: cmd) (s2: estate) := True.

Let Pfun (m1: mem) (fn: funname) (vargs: seq value) (m2: mem) (vres: seq value) := True.

Local Lemma Hskip : sem_Ind_nil Pc.
Proof.
  move=> s rmap1 rmap2 /= c2 [??] s' hv;subst rmap1 c2.
  exists s'; split => //; exact: Eskip. 
Qed.

Local Lemma Hcons : sem_Ind_cons P ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ Hi _ Hc sm1 _sm3 c1 /=;t_xrbindP => -[sm2 i'] hi [sm3 c'] hc /= ?? s1' hv. 
  subst c1 _sm3.
  have [s2' [si hv2]]:= Hi _ _ _ hi _ hv.
  have [s3' [sc hv3]]:= Hc _ _ _ hc _ hv2.
  exists s3'; split => //; apply: Eseq; [exact: si|exact: sc].
Qed.

Local Lemma HmkI : sem_Ind_mkI P ev Pi_r Pi.
Proof.
  move=> ii i s1 s2 _ Hi sm1 sm2 [ii' ir'] ha s1' hv.
  by have [s2' [Hs2'1 Hs2'2]] := Hi _ _ _ _ _ ha _ hv; exists s2'; split.
Qed.
(*
Lemma alloc_assgnP s1 s2 x tag ty e v v' ii1 ii2 i2 sm1 sm2:
  sem_pexpr gd s1 e = ok v -> 
  truncate_val ty v = ok v' -> 
  write_lval gd x v' s1 = ok s2 -> 
  Let ir := alloc_assgn nrsp gm sm1 ii1 x tag ty e in ok (ir.1, MkI ii1 ir.2) = ok (sm2, MkI ii2 i2) ->
  forall s1', valid sm1 s1 s1' → 
   ∃ s2', sem_i (sCP:= sCP_stack) P' rip s1' i2 s2' ∧ valid sm2 s2 s2'.
Proof.
  move=> hv htr Hw; rewrite /alloc_assgn.
  t_xrbindP => -[sm i'] e'; apply: add_iinfoP => he [sm' x'].
  apply: add_iinfoP => ha /= [?] ???? s1' hs1; subst i' sm sm' ii1 i2.
  have [v1 [He' Uvv1]] := alloc_eP he hs1 hv.
  have [v1' htr' Uvv1']:= truncate_value_uincl Uvv1 htr.
  have hty := truncate_val_has_type htr.
  have [s2' [Hw' Hs2']] := alloc_lvalP ha hs1 hty Uvv1' Hw.
  by exists s2'; split=> //;apply: Eassgn;eauto.
Qed.

  Lemma is_arr_typeP ty : is_arr_type ty -> exists n, ty = sarr n.
  Proof. case ty => //;eauto. Qed.

  Lemma is_varP e y: is_var e = Some y -> e = Pvar y.
  Proof. by case e => // ? [->]. Qed.

  Lemma find_gvar_set sm x ap z: 
    find_gvar gm (Mvar.set sm x ap) z = 
      if is_lvar z && (x == gv z) then Some (mp_of_ap ap) else find_gvar gm sm z.
  Proof.
    by rewrite /find_gvar; case: ifP => //= ?; rewrite Mvar.setP; case: ifP.
  Qed.
*)

Lemma is_sarrP ty : reflect (exists n, ty = sarr n) (is_sarr ty).
Proof.
  case: ty => /= [||n|ws]; constructor; try by move => -[].
  by exists n.
Qed.

Lemma get_set_region rmap x mp y :
  Mvar.get (var_region (set rmap x mp)) y = 
  if x == y then Some mp else Mvar.get (var_region rmap) y.
Proof. rewrite /set /= Mvar.setP; case: ifPn => // hne. Qed.

Lemma set_VALID rmap x mp: 
  valid_mp mp (vtype x) -> wfr_VALID rmap -> wfr_VALID (set rmap x mp).    
Proof.
  by move=> hv hV y mpy; rewrite get_set_region; case: eqP => [<- [<-]| _ /hV ].
Qed.

Lemma check_gvalid_set rmap x mp y: 
  check_gvalid (set rmap x mp) y = 
    if (x == (gv y)) && ~~is_glob y then Some mp 
    else check_gvalid rmap y.
Proof.
  rewrite /check_gvalid; case: ifPn => ? /=; first by rewrite andbF.
  rewrite andbT /check_valid get_set_region; case: eqP => [-> | hne].
  + by rewrite /set /= Mmp.setP_eq SvP.add_mem_1.
  case: Mvar.get => // mpy.
  rewrite /set /= Mmp.setP; case: eqP => // <-.
  by rewrite SvD.F.add_neq_b //; case: Mmp.get.
Qed.

Lemma set_VAL rmap x mp v s s': 
  eq_mp_val (vtype x) (emem s') mp (pto_val v) ->
  wfr_VAL rmap s s' -> 
  wfr_VAL (set rmap x mp) (with_vm s (evm s).[x <- ok v]) s'.
Proof.
  move=> hv hV y mpy vy; rewrite check_gvalid_set.
  case: ifPn => [ /andP[]/eqP heq /negP ? [<-]| ].
  + by subst x; rewrite get_gvar_eq /= => [[<-]| ].
  move=> h /hV hc;rewrite get_gvar_neq => [/hc // |/negP hn ].
  by move: h;rewrite hn andbT => /eqP. 
Qed.

Lemma type_of_get_var x vm v: get_var vm x = ok v → subtype (type_of_val v) (vtype x).
Proof.
  rewrite /get_var; apply on_vuP => // v' _ <-; apply subtype_type_of_val.
Qed.

Lemma type_of_get_gvar x gd vm v: get_gvar gd vm x = ok v → subtype (type_of_val v) (vtype (gv x)).
Proof.
  by rewrite /get_gvar; case: ifPn => [ ? /type_of_get_var | ? /type_of_get_global ->].
Qed.

Definition lea_ptr' y ptr ofs := 
  add (Pvar (mk_lvar (with_var y ptr))) (cast_const ofs).

Lemma get_addrP s1 s1' rmap1 rmap2 i2 x dx y:
  valid_state rmap1 m0 s1 s1' ->
  get_addr pmap rmap1 x dx y = ok (rmap2, i2) ->
  exists mp, 
    [/\ check_gvalid rmap1 y = Some mp,
        rmap2 = set rmap1 x mp &
        forall s2', write_lval [::] dx (Vword (mp_addr mp)) s1' = ok s2' ->
                     sem_i P' rip s1' i2 s2'].
Proof.
  move=> hvs; rewrite /get_addr /check_gvalid.   
  case: ifPn => hglob.             
  + t_xrbindP => ofs /get_globalP -> <- <- /=.
    exists {| mp_s := MSglob; mp_ofs := ofs |}.
    split => //= s2' hs; constructor.
    by rewrite /sem_sopn /= P'_globs /get_gvar /= vs_rip /= /sem_sop2 /= !zero_extend_u hs.
  case heq: get_local => [pk | //].         
  rewrite /set_move; t_xrbindP => rmap2' mp hva <- <- <-; rewrite hva.
  case /check_validP : hva => hgmp _.
  assert (h := wfr_ptr hgmp); case: h => pk' [];rewrite heq => -[?] hvp {heq}; subst pk'.
  exists mp; split => // s2' hs .
  case: pk hvp => /= [ofs | p | ofs] h.
  + subst mp; constructor.
    by rewrite /sem_sopn /= P'_globs /get_gvar /= vs_rsp /= /sem_sop2 /= !zero_extend_u hs.
  + by constructor; rewrite /sem_sopn /= P'_globs /get_gvar /= h /= !zero_extend_u hs.
  by constructor; rewrite /sem_sopn /= P'_globs vs_rsp /= !zero_extend_u h /= !zero_extend_u hs.
Qed.

Lemma alloc_array_moveP s1 s2 s1' rmap1 rmap2 x e v v' n i2 : 
  valid_state rmap1 m0 s1 s1' ->
  sem_pexpr gd s1 e = ok v ->
  truncate_val (sarr n) v = ok v' ->
  write_lval gd x v' s1 = ok s2 ->
  alloc_array_move pmap rmap1 x e = ok (rmap2, i2) → 
  ∃ s2' : estate, sem_i P' rip s1' i2 s2' ∧ valid_state rmap2 m0 s2 s2'.
Proof.
  move=> hvs he htr hw.
  rewrite /alloc_array_move.
  case: x hw => //= x.
  rewrite /write_var; t_xrbindP => vm1 hvm1 <- /=.
  have hu := value_uincl_truncate_val htr.
  have /type_of_val_arr := truncate_val_has_type htr.
  case => -[t ?];subst v'.
  + apply: set_varP hvm1.
    + by move=> ? /pof_val_undef_ok. 
    by move=> /is_sboolP h1 h2; elimtype False; move: h2; rewrite h1.
  apply: set_varP hvm1; last first.
  by move=> /is_sboolP h1 h2; elimtype False; move: h2; rewrite h1.
  case: x => -[[]// sx xn] xii /= t' [?] ?; subst t' vm1.
  set x := {|vname := xn|}.
  case: e he => //= y hy.
  have [sy [htyy hsy]]: exists sy, vtype (gv y) = sarr sy /\ n <= sy. 
  + have /= := subtype_trans (value_uincl_subtype hu) (type_of_get_gvar hy) .
    by case: vtype => // => sy /ZleP ?;eauto.
  have [sv [tv ? htv]] := value_uinclE hu; subst v.

  have heqma: forall mp, eq_mp_array (emem s1') mp sy (Varr tv) → 
                   eq_mp_array (emem s1') mp sx (Varr (WArray.inject sx t)).
  + rewrite /eq_mp_array => mp [tv' []] /Varr_inj [?]; subst sv => /= ? hgtv; subst tv'.
     eexists; split;first reflexivity.
     move=> off hoff v0 hget.
     have [hoffsy hgettv]: (off < sy)%Z /\  @WArray.get sy AAscale U8 tv off = ok v0.
     + move: hget; rewrite /WArray.get /CoreMem.read /= /wsize_size Z.mul_1_r /WArray.validr /WArray.validw /=.
       rewrite Z.add_0_r !andbT /CoreMem.uread /= /WArray.uget /WArray.add Z.add_0_r.
       rewrite WArray.zget_inject //; t_xrbindP => ??? /assertP hr /assertP -> /assertP.
       case: ZltP => // hlt hget hdec.  
       have -> /= : (WArray.in_range sy off U8).
       + move: hr;rewrite /WArray.in_range !zify /wsize_size; lia.
       case: htv => _ h; case heq: Mz.get hget hdec => [w | ] //= _.
       by rewrite (h _ _ _ heq); [ move=> <- /=;split => // | ]; lia.
     by apply hgtv => //; lia.

  case hglx : get_local => [[ofs | p | ofs] | //].
  + t_xrbindP => _ /assertP; rewrite is_lvar_is_glob => /negP hngy mpy hcvy.
    move=> _ /assertP -/eqP ???; subst mpy rmap2 i2.
    exists s1';split;first by constructor.
    case: (hvs) => vptr hdisj hrip hrsp hf heqvm hwfr heqg hnotm. 
    constructor => //.
    + move=> x1 hx1; rewrite -heqvm // get_var_neq //.
      by move=> heq;move: hx1;rewrite -heq hglx.
    case: (hwfr) => h1 h2 h3; constructor => //=.
    + by apply: set_VALID => //; exists x; split.
    + apply: set_VAL => //=.
      have : check_gvalid rmap1 y = Some {| mp_s := MSstack; mp_ofs := ofs |}.
      + by move/negP:hngy; rewrite /check_gvalid hcvy => /negbTE ->.
      by move=> /h2 -/(_ _ hy); rewrite htyy /=; apply heqma.
    move=> x1 mp1; rewrite get_set_region; case: eqP => [<- [<-]| _ /h3 //].
    rewrite hglx; move /check_validP: hcvy => [] /h3 [pk] [] ???.
    by exists (Pstack ofs).

  + move=> /get_addrP => -[mp [hcmp ?]]; subst rmap2.
    rewrite /write_lval /write_var /= /set_var.
    assert (hp := wt_rptr hglx) => {hglx}.
    rewrite (var_surj p) hp /=.
    move=> /(_ _ erefl) ?;eexists;split; first by eauto.
    case: (hvs) => vptr hdisj hrip hrsp hf heqvm hwfr heqg hnotm. 
    constructor => //.
    + assert (h:=disj_ptr).
    + 
    + move=> x1 hx1; rewrite -heqvm // get_var_neq //.
      by move=> heq;move: hx1;rewrite -heq hglx.
    case: (hwfr) => h1 h2 h3; constructor => //=.
    + by apply: set_VALID => //; exists x; split.
    + apply: set_VAL => //=.
      have : check_gvalid rmap1 y = Some {| mp_s := MSstack; mp_ofs := ofs |}.
      + by move/negP:hngy; rewrite /check_gvalid hcvy => /negbTE ->.
      by move=> /h2 -/(_ _ hy); rewrite htyy /=; apply heqma.
    move=> x1 mp1; rewrite get_set_region; case: eqP => [<- [<-]| _ /h3 //].
    rewrite hglx; move /check_validP: hcvy => [] /h3 [pk] [] ???.
    by exists (Pstack ofs).
    case: p hp => pty pn.
Search vtype.
Search set_var.
Search write_var.

  get_addrP
Print instr_r.

  + rewrite /get_addr.
   
       

Search g

Search _ check_valid.

hv hV y mpy; rewrite get_set_region; case: eqP => [<- [<-]| _ /hV ].
Print wfr_PTR.
          rewrite /eq_mp_array. => -[tv' []] /Varr_inj [?]. subst sv => /= ? hgtv; subst tv'.
          eexists; split;first reflexivity.
          move=> off hoff v0 hget.
  

          apply hgtv; first admit. 
Set Printing Implicit.
Set Printing Coer
          move: hget; rewrite /WArray.get /CoreMem.read /= /wsize_size Z.mul_1_r /WArray.validr /WArray.validw /=.
          rewrite Z.add_0_r !andbT /CoreMem.uread /= /WArray.uget /WArray.add Z.add_0_r.
          rewrite WArray.zget_inject //; t_xrbindP => ??? /assertP hr /assertP hal /assertP.
          case: ZltP => // hlt hget hdec.       
          have -> : (WArray.in_range sy off U8).
          + move: hr;rewrite /WArray.in_range !zify; lia.
          case:ifP =
            

Search WArray.inject.
          have : off < sy /\ WArray.get AAscale U8 t off = ok v0.
          + move: 
Print WArray.uincl.
          case: (ZltP off sy) => hoffsy.
          + apply hgtv. lia. 
            move: hget; rewrite /WArray.get /CoreMem.read /= /wsize_size Z.mul_1_r /WArray.validr /WArray.validw /=.
            rewrite /CoreMem.uread WArray.zget_inject Z.

Search WArray.inject.



sy < sx 

t : arr n
tv : arr sy

Print subtype.
          have := htv.          
rewrite /WArray.uincl.
Print WArray.inject.
          rewrite /WArray.get /CoreMem.read /= /wsize_size Z.mul_1_r.
          t_xrbindP.
          
Search CoreMem.read.
 hget.

Search WArray.get.
Search WArray.validr. 

          have /= []:= WArray.get_bound hget.
          rewrite /wsize_size.

          have := WArray.get_uget hget. rewrite /WArray.uget.
          Search WArray.uget.
Search eq_mp_val.
Print WArray.uincl.
Search _ value_uincl.

Search WArray.inject.
          have := h2 y.
rewrite /eq_mp_array.
Search eq_mp_val.

        + move=> x1 mp1 v1.

  get_gvar 
Print check_valid.
admit.
move=> ?.

  exists xs, 

 have := h2 x1 mp1 v1; rewrite /check_gvalid.
        case: ifPn => [ hg h /h| hng ]; first by rewrite get_gvar_neq ?hg.
        rewrite /check_valid.
admit.        
      + move=> x1.



        Print check_valid.
Lemma rm_setP x
Print rm_set.        
Print 
Search rm_set.

          + apply h1 => //. by apply /eqP.
          have := h1 _.
        Search _ Mvar.get Mvar.remove.
        case: 
Print get_local.
        Search remove.
Print valid_mp.
exists (mk_lvar {|v_var := x; v_info := xii|}).
Print valid_mp.
Search _ Mvar.get Mvar.set.
Check wfr_PTR_rset_word.
Print rset_word.
      + move=> y mpy v /(check_gvalid_rset_word hins hgetr) [].
        + move=> [ hng heq ?]; subst mpy.
          have -> : y = mk_lvar {|v_var := x; v_info := v_info (gv y) |}.
          + by case: y hng heq => -[yv vi] [] //= _ ->.
          have /= -> // := @get_gvar_eq gd (mk_lvar {| v_var := x; v_info := v_info (gv y) |}) (evm s1) (ok w).
          move=> [<-]; exists w';split;first by subst w.
          by apply: Memory.writeP_eq hmem2.
        move=> [hd hdm hcv]; rewrite get_gvar_neq // => /h2 -/(_ _ hcv) /=.
        by apply: (eq_mp_val_write_disj hvs hgetr) hmem2.
      by apply: wfr_PTR_rset_word hmem2 h3.
    + by apply: (eq_glob_rset_word hvs hgetr) hmem2 heqg.
    by apply: (eq_not_mod_rset_word hvs hgetr) hmem2 hnotm.


Search _ is_lvar.
Print is_Pvar.
Search _ is_Pvar.
Print is_lv_var.
Search _ is_lv_var.

Local Lemma Hassgn : sem_Ind_assgn P Pi_r.
Proof.
  move=> s1 s2 x tag ty e v v' hv htr hw rmap1 rmap2 ii1 ii2 i2 /=.
  t_xrbindP => -[rmap2' i2'] h /= ??? s1' hvs; subst rmap2' ii1 i2'.
  have htyv':= truncate_val_has_type htr.
  case: ifPn h => [/is_sarrP [n ?]| _ ].
  + subst ty; apply: add_iinfoP.


    admit.
  t_xrbindP => e'; apply: add_iinfoP => /(alloc_eP hvs) he [rmap2' x'].
  apply: add_iinfoP => hax /= ??; subst rmap2' i2.
  have [s2' [/= hw' hvs']]:= alloc_lvalP hax hvs htyv' hw.
  exists s2';split => //.
  apply: Eassgn; eauto; rewrite P'_globs; auto.
Qed.
  assert (hx := alloc_lvalP hax).
Check add_iinfoP.

Search add_iinfo.
    case:x hv htr Hw => [??| x|???|????]; try by apply: alloc_assgnP.
(*    case: ifP => hty. last by apply: alloc_assgnP.
    case he : is_var => [y | ]; last by apply: alloc_assgnP.
    case: ifP => hsubty; last by apply: alloc_assgnP.
    case hf : find_gvar => [mp | ]; last by apply: alloc_assgnP.
    move=> hv htr Hw; have [n htyx] := is_arr_typeP hty; have ? := is_varP he; subst e.
    set x' := {| v_var := _ |}.
    t_xrbindP => -[_sm2 _i2] _tt; apply: add_iinfoP=> /check_vfresh_lvalP [hnrsp hnrip] [??] /= ??? s1' hva.
    subst _sm2 ii1 _i2 i2 sm2; have := valid_s hva y. 
    rewrite hf => -[h1 h2].
    set s2' := {| emem := emem s1';
                  evm := (evm s1').[x' <- ok (@Build_pword U64 U64 
                                               (wptr (mp_s mp) + wrepr U64 (mp_ofs mp))
                                               (erefl true))] |}.
    exists s2'; split.
    + case hid: mp_id h1 => [idx | ] /= h1.
      + apply: S.Eassgn => /=;eauto.
        + by rewrite /truncate_val /= zero_extend_u; auto.
        done.
      apply: S.Eopn; rewrite /sem_sopn /= /get_gvar /= (get_vptr hva) /= /s2'. 
      by do 5! f_equal;rewrite !zero_extend_u wrepr0 wrepr1; ssrring.ssring.
    move: Hw; apply rbindP =>vm1 /=; apply: set_varP;rewrite /set_var; last by rewrite {1}htyx.
    move=> t ht ?[?]; subst vm1 s2.
    move: hv; rewrite /= /s2' /x' => {s2' x'}.
    case: x hnrsp hnrip hty htyx hsubty t ht => -[xty xn] xi /= hnrsp hnrip hty htyx hsubty t ht /=.
    subst xty; case: v' htr ht => // n' a'; last first.
    + by rewrite /pof_val /=; case: (n').
    rewrite /truncate_val; t_xrbindP; case: ty => //= n1 yt.
    case: v => //=;last by case.
    move=> ny ty1 /=; rewrite /WArray.cast; case: ifP => // /ZleP hn1 [?].
    move=> /Varr_inj [?]; subst n1 => /= ? [?] hgety; subst yt t a'. 
    have hyty: vtype (gv y) = sarr ny.  
    + move: hgety; rewrite /get_gvar; case: ifP => ?.
      + rewrite /get_var; apply on_vuP => //.
        by case: (gv y) => -[] [] //= p ???? /Varr_inj [?]; subst p. 
      by rewrite /get_global; case: get_global_value => // ?; case: eqP => // <- [->].
    move: hsubty; rewrite hyty /= => /ZleP hsubty.
    case: hva => hd her hdef hvm hrip hrsp htop hfr hs hm hg {h1 he}; split => //=.
    + move=> z /= /Sv_memP hin; rewrite !Fv.setP_neq; first last.
      + by apply /eqP; SvD.fsetdec. + by apply /eqP; SvD.fsetdec.
      by apply: hvm; apply /Sv_memP; SvD.fsetdec.
    + by rewrite get_var_neq // => h; move: hnrip; rewrite h /is_vrip eq_refl.
    + by rewrite get_var_neq // => h; move: hnrsp; rewrite h /is_vrsp eq_refl.
    + move=> z; case heq: find_gvar => [mpz | //]; move: heq.
      rewrite find_gvar_set; case: andP => [ [hlv /eqP heq] [?]| hna].
      + subst mpz => /=; split; first by rewrite /get_var Fv.setP_eq.
        move: h2; rewrite -heq /= hyty => h off hoff.
        have hoff' : 0 <= off ∧ off < ny by lia.
        have [h1 /(_ _ _ hgety) h2]:= h _ hoff'; split => //.
        rewrite /get_gvar hlv -heq /get_var Fv.setP_eq /= => s' a hok. 
        have /Varr_inj [? {hok}]:= ok_inj hok.
        subst s' => /= ? v hv; subst a; apply h2. 
        apply: WArray.uincl_get hv; split => // i vi hi.
        by rewrite WArray.zget_inject //=; case: ifP.
      move=> /find_gvar_keep [hz hdiff] /=.
      have := hs z; rewrite hz => -[hz1 hz2]; split.
      + case: mp_id hdiff hz1 => // id hne.
        by rewrite get_var_neq // => -[eid]; apply hne;rewrite eid.
      case: vtype hz2 => //.
      + move=> p hp off; rewrite get_gvar_neq; first by apply hp.
        by move=> his; apply /negP => he;auto.
      move=> w [hw1 hw2]; split => // v; rewrite get_gvar_neq; first by apply hw2.
      by move=> his; apply /negP => he;auto.
    move=> z mpz; have := hm _ _ hf; rewrite hyty => -[nn [[?]]]; subst nn.
    move=> [hmp1 hmp2 hmp3 hmp4].
    rewrite find_gvar_set;case: andP => [ [hlv /eqP heq] [?]| hna].
    + subst mpz => /=; exists n; rewrite -heq /=; split => //; split => //; first by lia.
      move=> z1 mpz1 sz1;rewrite find_gvar_set;case: andP => [ [hlv1 /eqP heq1] [?]| hna1].
      + by subst mpz1; rewrite /= eq_refl -heq1 /= => ?? [].
      move=> /find_gvar_keep [hz1 hdiff] /= hsz hms. 
      have := hmp4 _ _ _ hz1 hsz hms; case:eqP;last by lia.
      move=> ? h1 [ //| hh1]; have heq1 := h1 (or_intror hh1).
      by move: hh1; rewrite -heq1 hyty.
    move=> /find_gvar_keep [hz1 hdiff].
    have [sz1 [hsz1 [hmpz1 hmpz2 hmpz3 hmpz4]]]:= hm _ _ hz1; exists sz1; split => //; split => //.
    move => s mps ss;rewrite find_gvar_set;case: andP => [ [hlv1 /eqP heq1] [?]| hna1].
    + subst mps => /=; rewrite -heq1 /= => -[?] h1; subst ss.
      have := hmp4 _ _ _ hz1 hsz1; rewrite h1 => /(_ erefl); rewrite eq_sym.
      case: eqP => ?; last lia.
      move=> h [ hh1| //]; have heq2 := h (or_intror hh1).
      by move: hh1; rewrite -heq2 hyty.
    move=> /find_gvar_keep [hh1 hh2 hh3 hh4].
    by apply: hmpz4 hh1 hh3 hh4. *)
  Qed.
  
  Local Lemma Hopn : sem_Ind_opn P Pi_r.
  Proof.
    move => s1 s2 t o xs es.
    rewrite /sem_sopn;t_xrbindP => vs va He Hop Hw sm1 sm2 ii1 ii2 i2 /=.
    t_xrbindP => -[sm3 i'] es'; apply: add_iinfoP => he [sm4 x']; apply: add_iinfoP => ha /= [??] ??? s1' hv.
    subst i' sm3 sm4 ii1 i2.
    have [va' [He' Uvv']] := (alloc_esP he hv He). 
    have [w' [Hop' Uww']]:= vuincl_exec_opn Uvv' Hop.
    have [s2' [Hw' Hvalid']] := alloc_lvalsP ha hv (sopn_toutP Hop) Uww' Hw.
    exists s2'; split=> //.
    by apply: Eopn;rewrite /sem_sopn He' /= Hop'.
  Qed.

  Lemma valid_incl sm1 sm2 s s' :
    incl sm1 sm2 -> valid sm2 s s' -> valid sm1 s s'.
  Proof.
    rewrite /incl => /andP [] /allP hall 
      /Sv.subset_spec hsub [hd her hdef hvm hrip hrsp htopf hs hm hg].
    have h: forall x mpx, find_gvar gm sm1 x = Some mpx -> find_gvar gm sm2 x = Some mpx.
    + move=> x mpx; rewrite /find_gvar; case: ifP => //.
      case heq: (Mvar.get sm1 (gv x)) => [ap | //].
      have /hall : (v_var (gv x), ap) \in Mvar.elements sm1.(mstk) by apply /Mvar.elementsP.
      by rewrite /incl_alloc_pos /=; case : Mvar.get => // ap' /eqP <-.
    split => //.
    + by move=> x /Sv_memP hin; apply hvm; apply /Sv_memP; SvD.fsetdec.
    + move=> x; have := hs x; case heq : (find_gvar gm sm1 x) => [mp |// ].
      by rewrite (h _ _ heq).
    move=> x mpx /h hf; have [sx [? [??? h1]]]:= hm x mpx hf.
    by exists sx;split => //;split => // y mpy sy /h; apply h1.
  Qed.
    
  Lemma incl_merge_l sm1 sm2 : incl (merge sm1 sm2) sm1.
  Proof.
    rewrite /merge; apply /andP => /=; split; last by apply SvP.inter_subset_1.
    apply /allP => -[x ap] /Mvar.elementsP.
    rewrite Mvar.map2P //= /incl_alloc_pos.
    case: Mvar.get => [ap1| //]; case: Mvar.get => [ap2 | ] //=.
    by case: eqP => [-> | //] [->].
  Qed.

  Lemma incl_merge_r sm1 sm2 : incl (merge sm1 sm2) sm2.
  Proof.
    rewrite /merge; apply /andP => /=; split; last by apply SvP.inter_subset_2.
    apply /allP => -[x ap] /Mvar.elementsP.
    rewrite Mvar.map2P //= /incl_alloc_pos.
    case: Mvar.get => [ap1| //]; case: Mvar.get => [ap2 | ] //=.
    by case: eqP => [-> | //] [->].
  Qed.

  Lemma incl_refl sm : incl sm sm.
  Proof.
    apply /andP; split; last by apply SvP.subset_refl.
    apply /allP => -[x ap] /Mvar.elementsP /= h.
    by rewrite /incl_alloc_pos h.
  Qed.

  Lemma incl_trans sm1 sm2 sm3: incl sm1 sm2 -> incl sm2 sm3 -> incl sm1 sm3.
  Proof.
    move=> /andP [/allP a1 s1] /andP [/allP a2 s2]; apply /andP; split.
    + apply /allP => -[x ap] /a1 /=; rewrite /incl_alloc_pos.
      case heq :  Mvar.get => [ap2| //] /eqP ?;subst ap2.
      by apply: (a2 (x, ap)); apply /Mvar.elementsP.
    apply: SvP.subset_trans s1 s2.
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true P ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 Hse ? Hc sm1 sm2 ii1 ii2 i2 /=.
    t_xrbindP => -[sm3 i'] e'; apply: add_iinfoP => he [sm4 c1'] hc1 [sm5 c2'] hc2 /= [??]??? s1' hv.
    subst sm3 i' sm2 ii1 i2.
    have [b [he']]:= alloc_eP he hv Hse.
    move=> /value_uincl_bool /= -/(_ _ erefl) [_ ?];subst b.
    have [s2' [Hsem Hvalid']] := Hc _ _ _ hc1 _ hv.
    exists s2'; split; first by apply: Eif_true.
    by apply: valid_incl Hvalid'; apply incl_merge_l.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false P ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 Hse ? Hc sm1 sm2 ii1 ii2 i2 /=.
    t_xrbindP => -[sm3 i'] e'; apply: add_iinfoP => he [sm4 c1'] hc1 [sm5 c2'] hc2 /= [??]??? s1' hv.
    subst sm3 i' sm2 ii1 i2.
    have [b [he']]:= alloc_eP he hv Hse.
    move=> /value_uincl_bool /= -/(_ _ erefl) [_ ?];subst b.
    have [s2' [Hsem Hvalid']] := Hc _ _ _ hc2 _ hv.
    exists s2'; split; first by apply: Eif_false.
    by apply: valid_incl Hvalid'; apply incl_merge_r.
  Qed.

  Lemma loop2P ii check_c2 n sm sm' e' c1' c2': 
    loop2 ii check_c2 n sm = ok (sm', (e', (c1', c2'))) ->
    exists sm1 sm2, incl sm1 sm /\ check_c2 sm1 = ok ((sm', sm2), (e', (c1', c2'))) /\ incl sm1 sm2.
  Proof.
    elim: n sm => //= n hrec sm; t_xrbindP => -[[sm1 sm2] [e1 [c11 c12]]] hc2 /=; case: ifP.
    + move=> hi [] ????;subst.
      by exists sm; exists sm2;split => //; apply incl_refl.
    move=> _ /hrec [sm3 [sm4 [h1 [h2 h3]]]]; exists sm3, sm4; split => //.
    by apply: (incl_trans h1); apply incl_merge_l.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true P ev Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c1 e c2 _ Hc1 Hv ? Hc2 ? Hwhile sm1 sm2 ii1 ii2 i2 /=.
    t_xrbindP => -[sm3 i'] [sm4 [e' [c1' c2']]] /loop2P [sm5 [sm6 [hincl1 []]]].
    t_xrbindP => -[sm7 c11] hc1 /= e1; apply: add_iinfoP => he [sm8 c22] /= hc2 ????? hincl2 [??]???.
    subst i2 ii1 sm3 sm4 i' sm7 sm8 e1 c11 c22 => s1' /(valid_incl hincl1) hv. 
    have [s2' [hs1 hv2]]:= Hc1 _ _ _ hc1 _ hv.
    have [b [he']] := alloc_eP he hv2 Hv.
    move=> /value_uincl_bool /= -/(_ _ erefl) [_ ?];subst b.
    have [s3' [hs2 /(valid_incl hincl2) hv3]]:= Hc2 _ _ _ hc2 _ hv2.
    have /= := Hwhile sm5 sm2 ii2 ii2 (Cwhile a c1' e' c2').
    rewrite Loop.nbP /= hc1 /= he /= hc2 /= hincl2 /= => /(_ erefl _ hv3) [s4'] [hs3 hv4].
    by exists s4';split => //; apply: Ewhile_true; eauto.
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false P ev Pc Pi_r.
  Proof.
    move=> s1 s2 a c1 e c2 _ Hc1 Hv sm1 sm2 ii1 ii2 i2 /=.
    t_xrbindP => -[sm3 i'] [sm4 [e' [c1' c2']]] /loop2P [sm5 [sm6 [hincl1 []]]].
    t_xrbindP => -[sm7 c11] hc1 /= e1; apply: add_iinfoP => he [sm8 c22] /= hc2 ????? hincl2 [??]???.
    subst i2 ii1 sm3 sm4 i' sm7 sm8 e1 c11 c22 => s1' /(valid_incl hincl1) hv. 
    have [s2' [hs1 hv2]]:= Hc1 _ _ _ hc1 _ hv.
    have [b [he']] := alloc_eP he hv2 Hv.
    move=> /value_uincl_bool /= -/(_ _ erefl) [_ ?];subst b.
    by exists s2';split => //; apply: Ewhile_false; eauto.
  Qed.

  Local Lemma Hfor : sem_Ind_for P ev Pi_r Pfor.
  Proof. by []. Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof. by []. Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons P ev Pc Pfor.
  Proof. by []. Qed.

  Local Lemma Hcall : sem_Ind_call P ev Pi_r Pfun.
  Proof. by []. Qed.

  Local Lemma Hproc : sem_Ind_proc P ev Pc Pfun.
  Proof. by []. Qed.

  Lemma check_cP s1 c s2: sem P ev s1 c s2 -> Pc s1 c s2.
  Proof.
    apply (@sem_Ind _ _ _ P ev Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.
End PROOF.

Definition valid_map1 (m:Mvar.t Z) (size:Z) :=
  forall x px, Mvar.get m x = Some px -> 
     exists sx, size_of (vtype x) = ok sx /\
     [/\ 0 <= px, px + sx <= size,
      aligned_for (vtype x) px &
         forall y py sy, x != y -> 
           Mvar.get m y = Some py -> size_of (vtype y) = ok sy ->
           px + sx <= py \/ py + sy <= px].

Lemma init_mapP l sz m :
  init_map sz l = ok m -> 
  valid_map1 m sz.
Proof.
  rewrite /init_map.
  set f1 := (f in foldM f _ _ ).
  set g := (g in foldM _ _ _ >>= g). 
  have : forall p p',
    foldM f1 p l = ok p' -> 
    valid_map1 p.1 p.2 -> 0 <= p.2 ->
    (forall y py sy, Mvar.get p.1 y = Some py ->
        size_of (vtype y) = ok sy -> py + sy <= p.2) ->
    (p.2 <= p'.2 /\ valid_map1 p'.1 p'.2).
  + elim:l => [|[v pn] l Hrec] p p'//=.
    + by move=>[] <- ???;split=>//;omega.
    case:ifPn=> //= /Z.leb_le Hle.
    case: ifP => // Hal.
    case Hs : size_of=> [svp|]//= /Hrec /= {Hrec}Hrec H2 H3 H4. 
    have Hpos := size_of_pos Hs.
    case:Hrec.
    + move=> x px;rewrite Mvar.setP;case:ifPn => /eqP Heq.
      + move=> [] ?;subst;exists svp;split=>//;split => //.
        + omega. + omega.
        move=> y py sy Hne.
        by rewrite Mvar.setP_neq // => /H4 H /H ?;omega.
      move=> /H2 [sx] [Hsx] [] Hle0 Hpx Hal' Hy;exists sx;split=>//;split=>//.
      + omega.
      move=> y py sy Hne;rewrite Mvar.setP;case:eqP=> [?[]? |].
      + subst;rewrite Hs => -[] ?;subst; omega.
      by move=> Hney;apply Hy.
    + omega.
    + move=> y py sy;rewrite Mvar.setP;case:eqP=> [?[]?|].
      + subst;rewrite Hs => -[] ->;omega.
      move=> ? /H4 H /H ?;omega.
    move=> Hle2 H';split=>//;first by omega.
  move=> H;case Heq : foldM => [p'|]//=.
  case: (H _ _ Heq)=> //= Hp' Hv.
  rewrite /g; case:ifP => //= /Z.leb_le Hp [<-].
  move=> x px Hx.
  case :(Hv x px Hx) => //= sx [] Hsx [] H1 H2 H3 H4.
  by exists sx;split=>//;split=>//;omega.
Qed.

Lemma getfun_alloc nrsp oracle oracle_g (P:uprog) (SP:sprog) :
  alloc_prog nrsp oracle oracle_g P = ok SP ->
  exists lg mglob, 
    [/\ init_map (Z.of_nat (size SP.(p_extra).(sp_globs))) lg = ok mglob,
        check_globs (p_globs P) mglob SP.(p_extra).(sp_globs) &
        forall fn fd,
        get_fundef (p_funcs P) fn = Some fd ->
        exists fd', 
           get_fundef SP.(p_funcs) fn = Some fd' /\
           alloc_fd nrsp SP.(p_extra).(sp_rip) mglob oracle (fn, fd) = ok (fn,fd')].
Proof.
  rewrite /alloc_prog.
  case: (oracle_g P) => -[data rip] l.
  t_xrbindP => mglob; apply: add_err_msgP => heq.
  case heq1: check_globs => //; t_xrbindP => sfd hm ?; subst SP => /=.
  exists l, mglob;split => //.
  elim: (p_funcs P) sfd hm => [ | [fn1 fd1] fs hrec sfd] //=.
  t_xrbindP => -[fn2 fd2] fd2' H [??]; subst fn2 fd2'.
  move => sfds /hrec hm ?; subst sfd.
  move=> fn3 fd3 /=.
  case: eqP => ? .
  + by move=> [?]; subst fn3 fd3; exists fd2; rewrite H.
  by move=> /hm.
Qed.

Definition extend_mem (m1:mem) (m2:mem) (rip:pointer) (data: seq u8) :=
  let glob_size := Z.of_nat (size data) in
  [/\ wunsigned rip + glob_size <= wbase U64 /\
      (forall ofs s, is_align (rip + wrepr _ ofs) s = is_align (wrepr _ ofs) s), 
      (forall w sz, valid_pointer m1 w sz -> read_mem m1 w sz = read_mem m2 w sz),
      (forall w sz, valid_pointer m1 w sz ->
          ~((wunsigned rip <? wunsigned w + wsize_size sz) && (wunsigned w <? wunsigned rip + glob_size))),
      (forall w sz, valid_pointer m2 w sz = 
         valid_pointer m1 w sz || (between rip glob_size w sz && is_align w sz)) &
      (forall i, 
         0 <= i < glob_size ->
         read_mem m2 (rip + wrepr U64 i) U8 = ok (nth (wrepr U8 0) data (Z.to_nat i)))].

Lemma all_In (T:Type) (P: T -> bool) (l:seq T) x :
  all P l ->
  List.In x l -> P x.
Proof. by elim: l => //= x' l hi /andP [] hp /hi h -[<- | /h]. Qed.

Lemma valid_top (P : uprog) nrsp (stk_size : Z) (rsp : u64) (glob_size : Z) 
         (rip : u64) (data : seq u8) (gm : gmap) (sm : smap) 
         s1 s2 :
         valid P nrsp stk_size rsp glob_size rip data gm sm s1 s2 ->
 top_stack (emem s2) = rsp.
Proof.
  by move=> /valid_top_frame; rewrite /top_stack; case: frames => //= ?? [->].
Qed.

Lemma alloc_prog_stk_id nrsp oracle oracle_g P SP :
  alloc_prog nrsp oracle oracle_g P = ok SP →
  sp_stk_id SP.(p_extra) = nrsp.
Proof.
  by rewrite /alloc_prog; case: (oracle_g _) => - []; t_xrbindP => ?????; case: ifP => // _; t_xrbindP => ?? <-.
Qed.

Lemma alloc_fdP nrsp oracle oracle_g (P:uprog) SP fn fd fd':
  alloc_prog nrsp oracle oracle_g P = ok SP ->
  get_fundef (p_funcs P) fn = Some fd ->
  get_fundef (p_funcs SP) fn = Some fd' ->
  forall ev m1 va m1' vr rip, 
    sem_call P ev m1 fn va m1' vr ->
    forall m2, extend_mem m1 m2 rip SP.(p_extra).(sp_globs) ->
    (exists p, alloc_stack m2 (sf_stk_sz fd'.(f_extra)) = ok p) ->
    exists m2' vr',
      List.Forall2 value_uincl vr vr' /\
      extend_mem m1' m2' rip SP.(p_extra).(sp_globs) /\
      sem_call (sCP:=sCP_stack) SP rip m2 fn va m2' vr'.
Proof.
  move=> hap get Sget. 
  have ? := alloc_prog_stk_id hap; subst nrsp.
  have [lg [mglob [higlob hcheck hf]]]:= getfun_alloc hap.
  have [fd1 [] {hf}]:= hf _ _ get.
  rewrite Sget => -[?];subst fd1.
  rewrite /alloc_fd.
  case: (oracle (fn, fd)) => -[stk_size lv] ptrreg_of_reg .
  t_xrbindP => fd1 mstk; rewrite /add_err_fun.
  case histk : init_map => [mstk1 | //] [?]; subst mstk1.
  set gm := {| rip := _ |}; set sm0 := {| mstk := _ |}.
  move=> sm1; case hfold : foldM => [sm1' | //] [?]; subst sm1'.
  move=> [sme c]; apply: add_finfoP => hc /=.
  case: andP => // -[] hneq hres [?] ?;subst fd1 fd' => /=.
  move=> ev m1 vargs m1' vres rip hcall m2 hm2 [m2s ha].
  pose glob_size := Z.of_nat (size (sp_globs SP.(p_extra))).
  have Hstk: ptr_ok (top_stack m2s) stk_size.
  + by move: ha=> /Memory.alloc_stackP [].
  have Hglob: ptr_ok rip (Z.of_nat (size (sp_globs SP.(p_extra)))).
  + by rewrite /ptr_ok; case hm2.

  have hv : valid_map gm sm0 stk_size glob_size.
  + rewrite /sm0 => x mpx; rewrite /find_gvar /=; case:ifP => his.
    + rewrite Mvar.mapP; case heq: Mvar.get => [ofsx | // ] [?]; subst mpx.
      have [sx [h1 [h2 h3 h4 h5]]] := init_mapP histk heq.
      exists sx;split => //; split => //.
      move=> y mpy sy; case: ifP => his'.
      + rewrite  Mvar.mapP; case heq': Mvar.get => [ofsy | // ] [?]; subst mpy => /=.
        move=> hsy _; case: (v_var (gv x) =P gv y).
        + by move => heq1; move: heq'; rewrite -heq1 heq => -[->]; rewrite eq_refl.
        move=> /eqP => heq1; have := h5 _ _ _ heq1 heq' hsy; case: eqP => //.
        by have := size_of_pos h1; have := size_of_pos hsy; lia.
      by case: Mvar.get => [ofsy | //] [<-].
    case heq: Mvar.get => [ofsx' | // ] [?]; subst mpx => /=.
    have [sx [h1 [h2 h3 h4 h5]]] := init_mapP higlob heq.
    exists sx;split => //; split => //.
    move=> y mpy sy; case: ifP => his'.
    + by rewrite  Mvar.mapP; case heq': Mvar.get => [ofsy | // ] [?]; subst mpy.
    case heq': Mvar.get => [ofsy | //] [?] hsy _; subst mpy => /=.
    case: (v_var (gv x) =P gv y).
    + by move => heq1; move: heq'; rewrite -heq1 heq => -[->]; rewrite eq_refl.
    move=> /eqP => heq1; have := h5 _ _ _ heq1 heq' hsy; case: eqP => //.
    by have := size_of_pos h1; have := size_of_pos hsy; lia.
  have heq_init :
    init_state (semCallParams := sCP_stack) {| sf_stk_sz := stk_size; sf_extra := ptrreg_of_reg |} 
                          SP.(p_extra) rip {| emem := m2; evm := vmap0 |} = 
    ok {| emem := m2s; evm := vmap0.[vrsp (sp_stk_id SP.(p_extra)) <- ok (pword_of_word (top_stack m2s))]
                                             .[vrip gm <- ok (pword_of_word rip)] |}.
  + rewrite /init_state /= /init_stk_state ha /= /with_vm //=. 
    f_equal; f_equal; f_equal; [f_equal | ]; f_equal; rewrite /pword_of_word;
    f_equal; apply (Eqdep_dec.UIP_dec Bool.bool_dec).
    
  have hvalid : 
    valid P (sp_stk_id SP.(p_extra)) stk_size (top_stack m2s) 
            (Z.of_nat (size (sp_globs SP.(p_extra)))) rip (sp_globs SP.(p_extra)) gm sm0
              {| emem := m1; evm := vmap0 |}
              {| emem := m2s; evm := vmap0.[vrsp (sp_stk_id SP.(p_extra)) <- ok (pword_of_word (top_stack m2s))]
                                             .[vrip gm <- ok (pword_of_word rip)] |}.
  + case: hm2 => halign2 hread_eq hdisj hval hglob.
    have [hin hread_eqs hvals hal hdisjs htopf]:= Memory.alloc_stackP ha.
    constructor => //=.
    + move=> w sz hw; split; last by apply hdisj.
      by have := hdisjs w sz; rewrite hval hw /= => /(_ erefl) -[] h; apply /negP /nandP;
        [left|right];apply /ZltP; lia.
    + by move=> w sz hw; rewrite (hread_eq _ _ hw) hread_eqs // hval hw.
    + by move=> w sz; rewrite hvals hval -orbA (orbC (_ && _)) orbA.
(*    + by move=> x hnin hnrsp hnrip;rewrite !Fv.setP_neq // eq_sym. *)
    + by rewrite /get_var Fv.setP_eq.
    + rewrite /get_var Fv.setP_neq ? Fv.setP_eq //.
      by apply/eqP => -[k]; move/eqP: hneq; rewrite k.
    + by rewrite htopf. 
    + move=> x; rewrite /find_gvar.
      case: ifP => his. 
      + rewrite Mvar.mapP; case heq: Mvar.get => [ofs /=| //];split => //.
        have := init_mapP histk heq. 
        case Htype: (vtype (gv x))=> [| |n| sz] // [sx /= [[?] [h1 h2 h3 h4]]]; subst sx.
        + move=> off hoff; rewrite hvals; split.
          + apply /orP; right; rewrite is_align8 andbT.
            rewrite /between wsize8 /ptr_size /wptr /= (wunsigned_rsp_add Hstk); [ | nia | nia ].
            by apply/andP; split; apply/ZleP; nia.
          move=> s' a; rewrite /get_gvar his /get_var Fv.get0 /on_vu /pundef_addr Htype /= => hok.
          by have /Varr_inj [e ?]:= ok_inj hok; subst s' a; rewrite WArray.get0.
        split.
        + rewrite hvals; apply /orP; right.
          have heq2 : v_var (gv x) = {| vtype := sword sz; vname := vname (gv x) |}.
          + by case: (v_var (gv x)) Htype => /= ?? ->.
          rewrite heq2 in heq. have /(_ sz (vname (gv x)) ofs):= valid_get_w Hstk Hglob hv. 
          by rewrite /sm0 /= Mvar.mapP heq /= /wptr /= => /(_ erefl).
        by move=> ?;rewrite /get_gvar his /get_var Fv.get0 /on_vu /pundef_addr Htype.
      rewrite /gm /=; case heq: Mvar.get => [ofs /=| //]; split => //.
      have := init_mapP higlob heq. 
      case Htype: (vtype (gv x))=> [| |n| sz] // [sx /= [[?] [h1 h2 h3 h4]]]; subst sx.
      + move=> off hoff; rewrite hvals.
        have hvalid : valid_pointer m2 (wptr (top_stack m2s) rip MSglob + wrepr U64 (off + ofs)) U8.
        + rewrite hval; apply /orP; right; rewrite is_align8 andbT.
          rewrite /between wsize8 /ptr_size /wptr (wunsigned_rip_add Hglob).
          + by apply/andP; split; apply/ZleP; nia.
          + nia.
          by move: (size _) hoff h2 h1; clear=> *;lia. 
        split; first by rewrite hvalid.
        move=> s' a; rewrite /get_gvar his /get_global /get_global_value.
        case heq1 : xseq.assoc => [ []//= | //]; case: eqP => //.
(*
        rewrite Htype => -[?] heq2; subst n'; have /Varr_inj [e ?] := ok_inj heq2; subst n a => /=.
        have := all_In hcheck (xseq.assoc_mem' heq1).
        rewrite /check_glob /= heq => /andP [hle /allP hall] v hget. 
        have := hall (Z.to_nat off); rewrite mem_iota /= Z2Nat.id; last by lia.
        rewrite hget.
        match goal with |- (?A -> _) -> _ => have hh: A end.
        + by apply /ltP; case: hoff => ? /Z2Nat.inj_lt;apply.
        move=> /(_ hh) {hh} /eqP <-.
        rewrite /wptr -hread_eqs;last by move: hvalid; rewrite /wptr /=.
        rewrite hglob; last by lia. 
        rewrite Z.add_comm Z2Nat.z2nD;first last.
        + by apply /lezP;rewrite -ssrring.z0E;lia.
        + by apply /lezP;rewrite -ssrring.z0E;lia. 
        by rewrite -nth_drop wrepr0. *)
      rewrite /valid_ptr_word /get_gvar /wptr his.
      have hvalid : valid_pointer m2 (rip + wrepr U64 ofs) sz.
      + rewrite hval; apply /orP; right.
        case: halign2 => hh1 hh2; rewrite /between hh2 h3 andbT.
        rewrite (wunsigned_rip_add Hglob) //.
        + apply /andP;split; apply /ZleP;lia.
        move: (size _) (@wsize_size_pos sz) h2 => *; lia. 
      rewrite hvals hvalid;split => // v. 
      rewrite -hread_eqs // /get_global /get_global_value Htype.
      case heq1 : xseq.assoc => [[ sz' w] //= | //]; case: eqP => // -[?] [?]; subst sz' v.
      exists w => //; rewrite Memory.readP /CoreMem.read.
      have := validr_valid_pointer m2 (rip + wrepr U64 ofs)%R sz.
      rewrite hvalid => /is_okP => -[? ->] /=.
      have := all_In hcheck (xseq.assoc_mem' heq1).
Opaque Z.to_nat.
      rewrite /check_glob heq /= => /andP [hh1 /eqP hh2];subst w.
      f_equal; f_equal.
      rewrite /CoreMem.uread; apply: (@eq_from_nth _ (wrepr U8 0)).
      have hw := @le0_wsize_size sz.
      + rewrite size_map size_ziota size_take size_drop.
        case: ifPn => // /ltP; rewrite Nat2Z.inj_lt Z2Nat.id // Nat2Z.n2zB; last first. 
        rewrite -(Nat2Z.id (size _)); apply /leP; rewrite -Z2Nat.inj_le; lia.
        rewrite -subZE Z2Nat.id // => hh. 
        have -> : (wsize_size sz) = Z.of_nat (size (sp_globs SP.(p_extra))) - ofs.
        + by move:(size _) h2 hh => *; lia.
        by rewrite Z2Nat.inj_sub // Nat2Z.id.
      move=> i; rewrite size_map size_ziota => hi.
      rewrite (nth_map 0) ?size_ziota // nth_take // nth_drop nth_ziota // Memory.addP /=.
      rewrite -GRing.addrA -wrepr_add.
      move /ltP: hi; rewrite Nat2Z.inj_lt Z2Nat.id // => hi.
      have : 0 <= ofs + Z.of_nat i ∧ ofs + Z.of_nat i < Z.of_nat (size (sp_globs SP.(p_extra))).
      + by move:(size _) h2 => *; lia.
      move=> /hglob; rewrite Memory.readP /CoreMem.read CoreMem.uread8_get. 
      t_xrbindP => ?? ->; rewrite Z2Nat.inj_add //; last by apply Zle_0_nat.
      by rewrite Nat2Z.id addP.
    move=> i [hi1 hi2]; rewrite -hread_eqs; first by apply hglob.
    rewrite hval is_align8 andbT;apply /orP;right.
    apply /andP;rewrite (wunsigned_rip_add Hglob) // wsize8;split;apply /ZleP; lia.
Transparent Z.to_nat.
  inversion_clear hcall.
  case: H1 (* init_state ... *) => ?;subst s0.
  move: H;rewrite get => -[?];subst f.
  have uvargs0 : List.Forall2 value_uincl vargs0 vargs0.
  + by apply List_Forall2_refl.
  have [s1' [hwargs hvalid2 ]] := check_lvarsP hvalid hfold uvargs0 H2.
  have hdisj : 0 < stk_size -> 0 < Z.of_nat (size (sp_globs SP.(p_extra))) ->
       ((wunsigned (top_stack m2s) + stk_size <=? wunsigned rip)
                || (wunsigned rip + Z.of_nat (size (sp_globs SP.(p_extra))) <=? wunsigned (top_stack m2s))).
  + case: hm2 =>  _ _ _ hvm2 _ hss hsg. 
    have [_ _ _ _ hh _]:= Memory.alloc_stackP ha.
    have /hh : valid_pointer m2 rip U8.
    + rewrite hvm2 is_align8 andbT;apply /orP;right.
      rewrite /between Z.leb_refl /= wsize8; apply /ZleP. 
      by move: (size _) hsg => *;lia.
    have /hh : valid_pointer m2 (rip + wrepr Uptr (Z.of_nat (size (sp_globs SP.(p_extra))) - 1)) U8.
    + rewrite hvm2 is_align8 andbT;apply /orP;right.
      rewrite /between (wunsigned_rip_add Hglob); [ | lia | lia]. 
      by rewrite wsize8; apply /andP; split; apply /ZleP; by move: (size _) hsg => *; lia.
    rewrite wsize8 (wunsigned_rip_add Hglob); [ | lia | lia]. 
    move=> a1 a2;apply /orP.
    rewrite /is_true !Z.leb_le. 
    case: a1; first by lia.
    case: a2; last by lia.
    move=> h_1 h_2.
    have u1 : stk_size < Z.of_nat (size (sp_globs SP.(p_extra))) by lia.
    have /hh : valid_pointer m2 (top_stack m2s) U8.
    + rewrite hvm2 is_align8 andbT;apply /orP;right.
      rewrite /between wsize8; apply /andP.
      move: (size _) h_1 h_2 => *; split; apply /ZleP; lia.
    by rewrite wsize8; lia.   
  have [s3 [hssem hvalid3]] := check_cP (P:= P) SP.(p_funcs) Hstk Hglob hdisj H3 hc hvalid2.
  have [vres1 [H1' uincl1]]:= check_varsP hres (valid_vm hvalid3) H4.
  have [vres2 htr uincl2]:= mapM2_truncate_val H5 uincl1.
  exists (free_stack (emem s3) stk_size), vres2.
  split => //; split.
  + have /Memory.free_stackP [h1 h2 h3 h4 (* h5 *)]: 
     omap snd (ohead (frames(emem s3))) = Some stk_size.
    + by rewrite (valid_top_frame hvalid3).
    have [u1 u2 u3 u4 u5] := hm2.
    have vdisj: forall w sz, valid_pointer m1' w sz ->  disjoint_zrange (top_stack m2s) stk_size w (wsize_size sz).
    + subst m1'; move=> w sz hw; have [ /negP /andP] := valid_disj hvalid3 hw.
      rewrite {1 2}/is_true !Z.ltb_lt => ??; split.
      + by apply /ZleP; case: Hstk.
      + by apply is_align_no_overflow; apply (Memory.valid_align hw).
      lia.
    subst m1';split => //.
    + move=> w sz hw.
      rewrite (valid_eq hvalid3) // h1 // h2 (valid_def hvalid3) /= hw /=; split=> //.
      by rewrite (valid_top hvalid3); apply vdisj.
    + by move=> w sz /(valid_disj hvalid3) [].
    + move=> w sz. 
      apply Bool.eq_iff_eq_true; have := h2 w sz.
      rewrite {1}/is_true => ->.
      rewrite (valid_def hvalid3) /= (valid_top hvalid3); split.
      + move=> [] /orP [].
        + move=> /orP [-> //| ].
          move=> /andP [] /andP [] /ZleP ? /ZleP ?? [???].
          by have := wsize_size_pos sz;lia.
        by move=> /andP [-> ->] /=;rewrite orbT.         
      move=> /orP [ hw | /andP [hb hal]]. 
      + by rewrite hw /=;split => //; apply: vdisj.
      rewrite hb hal !orbT;split => //; split.
      + by apply /ZleP; case: Hstk.
      + by apply is_align_no_overflow.
      have : valid_pointer m2 w sz by rewrite u4 hb hal /= orbT.
      have [_ _ _ _ h _]:= Memory.alloc_stackP ha.
      by move=> /h; lia.
    move=> i [hi1 hi2].
    rewrite -h1.
    + by rewrite (valid_glob hvalid3).
    rewrite h2 (valid_top hvalid3) (valid_def hvalid3) is_align8 !andbT; split.
    + apply /orP;right; apply /andP.
      rewrite (wunsigned_rip_add Hglob) // wsize8;split;apply /ZleP.
      lia. move: hi1 hi2; rewrite /h4; move: (size _) => *;lia.
    split.
    + by apply /ZleP; case: Hstk.
    + by apply is_align_no_overflow; apply is_align8.
    have :  valid_pointer m2 (rip + wrepr U64 i) U8.
    + rewrite u4 is_align8 andbT; apply /orP;right.
      by apply /andP; rewrite (wunsigned_rip_add Hglob) // wsize8;split;apply /ZleP;lia.
    have [_ _ _ _ h _]:= Memory.alloc_stackP ha.
    by move=> /h;lia.
  econstructor;eauto.
  move: hap hssem => /=; rewrite /alloc_prog.
  by case: oracle_g => -[???]; t_xrbindP => ??; case:ifP => // ?; t_xrbindP => ?? <-.
Qed.

Definition alloc_ok (SP:sprog) fn m2 :=
  forall fd, get_fundef (p_funcs SP) fn = Some fd ->
  allocatable_stack m2 fd.(f_extra).(sf_stk_max).

Lemma alloc_progP nrip data oracle_g oracle (P: uprog) (SP: sprog) fn:
  alloc_prog nrip data oracle_g oracle P = ok SP ->
  forall ev m1 va m1' vr rip, 
    sem_call (sCP := sCP_unit) P ev m1 fn va m1' vr ->
    forall m2, extend_mem m1 m2 rip SP.(p_extra).(sp_globs) ->
    alloc_ok SP fn m2 ->
    exists m2' vr',
      List.Forall2 value_uincl vr vr' /\
      extend_mem m1' m2' rip SP.(p_extra).(sp_globs) /\
      sem_call (sCP := sCP_stack) SP rip m2 fn va m2' vr'.
Proof.
  move=> Hcheck ev m1 va m1' vr rip hsem m2 he ha.
  have [fd hget]: exists fd, get_fundef (p_funcs P) fn = Some fd.
  + by case: hsem=> ??? fd *;exists fd.
  have [lg [mglob [higlob hcheck hf]]]:= getfun_alloc Hcheck.
  have [fd' [hgetS ?]]:= hf _ _ hget.
  by apply: (alloc_fdP Hcheck hget hgetS hsem he (ha _ hgetS)).
Qed.
