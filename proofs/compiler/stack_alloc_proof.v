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
                 --------------- ------------ --------------------
                 | other stack | |   glob   | |    mem source    |
                 --------------- ------------ --------------------

                                  ||
                                  || function call
                                  \/

   m:
   ------------- --------------- ------------ --------------------
   |   stack   | | other stack | |   glob   | |    mem source    |
   ------------- --------------- ------------ --------------------

*)

(* The memory zones that are not in a writable slot remain unchanged. *)
Definition mem_unchanged ms m0 m :=
  forall p, valid_pointer m0 p U8 -> ~ valid_pointer ms p U8 ->
  (forall s, Sv.In s Slots -> Writable s -> disjoint_zrange (Addr s) (size_slot s) p (wsize_size U8)) ->
  read_mem m0 p U8 = read_mem m p U8.

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
  wfs_align_ptr : (Uptr <= ws)%CMP;
  wfs_offset_align : is_align (wrepr _ z.(z_ofs))%R Uptr;
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
  wf_locals  : forall x pk, Mvar.get pmap.(locals) x = Some pk -> wf_local x pk;
  wf_vnew    : forall x pk, Mvar.get pmap.(locals) x = Some pk -> ~ Sv.In x pmap.(vnew)
}.

(* Declare Instance wf_pmapI : wf_pmap. *)

(* Well-formedness of a [region]. *)
Record wf_region (r : region) := {
  wfr_slot     : Sv.In r.(r_slot) Slots;
  wfr_writable : Writable r.(r_slot) = r.(r_writable);
  wfr_align    : Align r.(r_slot) = r.(r_align);
}.

(* Well-formedness of a [zone]. *)
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
Definition wfr_WF (rmap : region_map) :=
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

(* Registers (not introduced by the compiler) hold the same value in [vm1] and [vm2] *)
Definition eq_vm (vm1 vm2:vmap) := 
  forall (x:var),
    Mvar.get pmap.(locals) x = None ->
    ~ Sv.In x pmap.(vnew) ->
    get_var vm1 x = get_var vm2 x.

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
(* 
(* TODO : could we merge [eq_mp_word] and [eq_mp_array] ? *)
Definition eq_sub_region_word (m2:mem) sr bytes sz v := 
  exists w:word sz,
    v = Vword w /\
    (ByteSet.mem bytes (interval_of_zone (sub_zone_at_ofs sr.(sr_zone) (Some 0) (wsize_size sz))) ->
      read_mem m2 (sub_region_addr sr) sz = ok w).

Definition eq_sub_region_array (m2:mem) sr bytes s v := 
  exists (a:WArray.array s),
   v = Varr a /\
   forall off, (0 <= off < Zpos s)%Z ->
     ByteSet.memi bytes (sr.(sr_zone).(z_ofs) + off) ->
     forall v, WArray.get AAscale U8 a off = ok v ->
     read_mem m2 (sub_region_addr sr + wrepr _ off) U8 = ok v. *)

(* Definition get_val_byte v off :=
  match v with
  | Vword ws w => 
    let a := WArray.empty (Z.to_pos (wsize_size ws)) in
    Let a := WArray.set a AAscale 0 w in
    WArray.get AAscale U8 a off
  | Varr _ a => WArray.get AAscale U8 a off
  | _ => type_error
  end. *)

(* Size of a value. *)
Notation size_val v := (size_of (type_of_val v)).

(* This definition is not very elegant, but it enables to reuse results from
   [WArray] on words.
*)
Definition array_of_val (v : value) :=
  match v return result _ (WArray.array (Z.to_pos (size_val v))) with
  | Vword ws w => let a := WArray.empty (Z.to_pos (wsize_size ws)) in
                  Let a := WArray.set a AAscale 0 w in ok a
  | Varr _ a => ok a
  | _ => type_error
  end.

(* We read the sub-word of [v] of size [ws] at offset [off * mk_scale aa ws].
   This allows to deal uniformly with words and arrays.
*)
Definition get_val aa ws v off :=
  Let a := array_of_val v in
  WArray.get aa ws a off.

(* [get_val] specialized to read only one byte. *)
Definition get_val_byte := get_val AAscale U8.
(*
Definition get_val_byte v off :=
  match v with
  | Vword ws w => if ((0 <= off) && (off < wsize_size ws))%CMP then ok (nth 0%R (LE.encode w) (Z.to_nat off)) else type_error
  | Varr _ a => WArray.get AAscale U8 a off
  | _ => type_error
  end.
*)

Definition eq_sub_region_val_read (m2:mem) sr bytes v :=
  forall off,
     ByteSet.memi bytes (sr.(sr_zone).(z_ofs) + off) ->
     forall w, get_val_byte v off = ok w ->
     read_mem m2 (sub_region_addr sr + wrepr _ off) U8 = ok w.

Definition eq_sub_region_val ty m2 sr bytes v :=
  eq_sub_region_val_read m2 sr bytes v /\
  (* According to the psem semantics, a variable of type [sword ws] can store
     a value of type [sword ws'] of shorter size (ws' <= ws).
     But actually, this is used only for register variables.
     For stack variables, we check in [alloc_lval] in stack_alloc.v that the
     value has the same size as the variable, and we remember that fact here.
  *)
  (* Actually, it is handful to know that [ty] and [type_of_val v] are the same
     even in the non-word cases.
  *)
  type_of_val v = ty.

(*
Definition eq_sub_region_val ty (m2:mem) sr bytes v := 
  match ty with
  | sword ws => eq_sub_region_word m2 sr bytes ws v
  | sarr  s  => eq_sub_region_array m2 sr bytes s v 
  | _        => True
  end.*)

Variable (P: uprog) (ev: extra_val_t (progT := progUnit)).
Notation gd := (p_globs P).

(* FIXME : est-ce qu'on teste la bonne zone dans le cas skptr ?
   Doit-on tester une largeur de z_len ou plus précisément Uptr ?
*)
Definition valid_pk rmap (s2:estate) sr pk :=
  match pk with
  | Pdirect s ofs ws z sc =>
    sr = sub_region_direct s ws sc z
  | Pstkptr s ofs ws z f => (*
    let srf := sub_region_stkptr s ws z in
    let bytes := get_var_bytes rmap srf.(sr_region) f in
    let i := interval_of_zone (sub_zone_at_ofs z (Some 0) (wsize_size Uptr)) in
    ByteSet.mem bytes i -> *)
    check_stack_ptr rmap s ws z f ->
    read_mem s2.(emem) (sub_region_addr (sub_region_stkptr s ws z)) Uptr = ok (sub_region_addr sr)
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
    eq_sub_region_val x.(gv).(vtype) s2.(emem) sr bytes v.

Definition wfr_PTR (rmap:region_map) (s2:estate) :=
  forall x sr, Mvar.get (var_region rmap) x = Some sr ->
    exists pk, get_local pmap x = Some pk /\ valid_pk rmap s2 sr pk.

Class wf_rmap (rmap:region_map) (s1:estate) (s2:estate) := {  
(*   wfr_valid_mp :  wfr_VALID rmap; *)
  wfr_wf  : wfr_WF rmap;
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
  vs_unchanged  : mem_unchanged s1.(emem) m0 s2.(emem); (* is it correct? *)
  vs_rip        : get_var (evm s2) pmap.(vrip) = ok (Vword rip);
  vs_rsp        : get_var (evm s2) pmap.(vrsp) = ok (Vword rsp);
  vs_eq_vm      : eq_vm s1.(evm) s2.(evm);
  vs_wf_region  :> wf_rmap rmap s1 s2;
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

(* TODO: gd or [::] ? *)
Lemma mk_ofsP aa sz gd s2 ofs e i :
  sem_pexpr gd s2 e >>= to_int = ok i ->
  sem_pexpr gd s2 (mk_ofs aa sz e ofs) = ok (Vword (wrepr U64 (i * mk_scale aa sz + ofs)%Z)).
Proof.
  rewrite /mk_ofs; case is_constP => /= [? [->] //| {e} e he] /=.
  rewrite /sem_sop2 /=.
  have [sz' [w [-> /= -> /=]]]:= cast_wordP he.
  by rewrite !zero_extend_u wrepr_add wrepr_mul GRing.mulrC. 
Qed.

(* this is about two objects from [memory_example]. MOVE ? *)
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

(* TODO: gd or [::] ? *)
Lemma mk_ofsiP gd s e i aa sz :
  Let x := sem_pexpr gd s e in to_int x = ok i ->
  mk_ofsi aa sz e <> None ->
  mk_ofsi aa sz e = Some (i * mk_scale aa sz).
Proof. by case: e => //= _ [->]. Qed.

Section EXPR.
  Variables (rmap:region_map) (m0:mem) (s:estate) (s':estate).
  Hypothesis (hvalid: valid_state rmap m0 s s').

  (* If [x] is a register : it is not impacted by the presence of global
     variables per hypothesis [vs_eq_vm]
  *)
  Lemma get_var_kindP x v:
    get_var_kind pmap x = ok None ->
    ~ Sv.In x.(gv) pmap.(vnew) ->
    get_gvar gd (evm s) x = ok v ->
    get_gvar [::] (evm s') x = ok v.
  Proof.
    rewrite /get_var_kind; case: ifPn => hglob; first by t_xrbindP.
    case hgl : get_local => // _ /(vs_eq_vm hgl) heq.
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
  (* TODO : one way is to change all invariants from is_align to | and use is_align_mod *)
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
    if ofs is None then ty' else ty.

  (* Sans doute à généraliser pour n'importe quelle longueur *)
  (* wsize_size ws -> len *)
  Lemma sub_region_at_ofs_wf sr ty (* ws *) ofs ty2 (* len *) :
    wf_sub_region sr ty ->
    (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + size_of ty2 <= size_of ty) ->
    wf_sub_region (sub_region_at_ofs sr ofs (size_of ty2)) (stype_at_ofs ofs ty2 ty).
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

  Definition zbetween_zone z1 z2 :=
    (z1.(z_ofs) <=? z2.(z_ofs)) && (z2.(z_ofs) + z2.(z_len) <=? z1.(z_ofs) + z1.(z_len)).

  Lemma zbetween_zone_refl z : zbetween_zone z z.
  Proof. by rewrite /zbetween_zone !zify; lia. Qed.

  Lemma zbetween_zone_trans z1 z2 z3 :
    zbetween_zone z1 z2 ->
    zbetween_zone z2 z3 ->
    zbetween_zone z1 z3.
  Proof. by rewrite /zbetween_zone !zify; lia. Qed.

  (* FIXME: why are we using CMP on Z ?? *)
  (* TODO : put that lemma in zify ? *)
  Lemma Zcmp_le i1 i2 : (i1 <= i2)%CMP = (i1 <=? i2)%Z.
  Proof.
    rewrite /cmp_le /gcmp /Mz.K.cmp /Z.leb -Zcompare_antisym.
    by case: Z.compare.
  Qed.

  Lemma disjoint_zones_incl z1 z1' z2 z2' :
    zbetween_zone z1 z1' ->
    zbetween_zone z2 z2' ->
    disjoint_zones z1 z2 ->
    disjoint_zones z1' z2'.
  Proof. by rewrite /zbetween_zone /disjoint_zones !Zcmp_le !zify; lia. Qed.

  Lemma disjoint_zones_incl_l z1 z1' z2 :
    zbetween_zone z1 z1' ->
    disjoint_zones z1 z2 ->
    disjoint_zones z1' z2.
  Proof. by move=> ?; apply disjoint_zones_incl => //; apply zbetween_zone_refl. Qed.

  Lemma disjoint_zones_incl_r z1 z2 z2' :
    zbetween_zone z2 z2' ->
    disjoint_zones z1 z2 ->
    disjoint_zones z1 z2'.
  Proof. by move=> ?; apply disjoint_zones_incl => //; apply zbetween_zone_refl. Qed.

  Lemma subset_interval_of_zone z1 z2 :
    I.subset (interval_of_zone z1) (interval_of_zone z2) = zbetween_zone z2 z1.
  Proof.
    rewrite /I.subset /interval_of_zone /zbetween_zone /=.
    by apply /idP/idP; rewrite !zify; lia.
  Qed.

  (* The assumption on [ofs] is different from other lemmas (where we use
     [size_slot x] instead of [z.(z_len)] as upper bound), since we do not
     have a slot at hand. Is it a problem?
     -> this was changed
  *)
  Lemma zbetween_zone_sub_zone_at_ofs z ty sl ofs len :
    wf_zone z ty sl ->
    (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + len <= size_of ty) ->
    zbetween_zone z (sub_zone_at_ofs z ofs len).
  Proof.
    move=> hwf.
    case: ofs => [ofs|]; last by (move=> _; apply zbetween_zone_refl).
    move=> /(_ _ refl_equal).
    rewrite /zbetween_zone !zify /=.
    by have := hwf.(wfz_len); lia.
  Qed.

  (* We use [sub_zone_at_ofs z (Some 0)] to manipulate sub-zones of [z].
     Not sure if this a clean way to proceed.
     This lemma is a special case of [zbetween_zone_sub_zone_at_ofs].
  *)
  Lemma zbetween_zone_sub_zone_at_ofs_0 z ty sl :
    wf_zone z ty sl ->
    zbetween_zone z (sub_zone_at_ofs z (Some 0) (size_of ty)).
  Proof.
    move=> hwf.
    apply: (zbetween_zone_sub_zone_at_ofs hwf).
    by move=> _ [<-]; lia.
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

  Lemma check_validP (x : var_i) ofs (* ws *) len sr :
(*     let: len := wsize_size ws in *)
(*     (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + len <= size_slot x) -> *)
    check_valid rmap x ofs len = ok sr ->
    exists sr' bytes,
    [/\ check_gvalid rmap (mk_lvar x) = Some (sr', bytes),
    sr = sub_region_at_ofs sr' ofs len &
    let isub_ofs := interval_of_zone sr.(sr_zone) in
    ByteSet.mem bytes isub_ofs].
  Proof.
    rewrite /check_valid /check_gvalid.
    t_xrbindP=> (* hofs *) sr' /get_sub_regionP -> _ /assertP hmem <-.
    by eexists sr', _.
  Qed.

  Lemma check_vpkP x vpk ofs len sr :
    (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + len <= size_slot x.(gv)) ->
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
    + t_xrbindP => -[_ ws'] /get_globalP /dup [] /wf_globals /sub_region_glob_wf hwf -> <- [<-] /=.
      set sr' := sub_region_glob _ _.
      set bytes := ByteSet.full _.
      exists sr', bytes; split=> //.
      apply: subset_mem; last by apply mem_full.
      rewrite subset_interval_of_zone.
      by apply (zbetween_zone_sub_zone_at_ofs hwf).
    by case hlocal: get_local => [pk|//] [<-] /(check_validP).
  Qed.

  Lemma check_gvalid_wf x sr_bytes :
    wfr_WF rmap ->
    check_gvalid rmap x = Some sr_bytes ->
    wf_sub_region sr_bytes.1 x.(gv).(vtype).
  Proof.
    move=> hwfr.
    rewrite /check_gvalid; case: (@idP (is_glob x)) => hg.
    + by case heq: Mvar.get => [[??]|//] [<-] /=; apply (sub_region_glob_wf (wf_globals heq)).
    by case heq: Mvar.get => // -[<-]; apply hwfr.
  Qed.

  Lemma check_vpk_wordP x vpk ofs ws t :
    (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + wsize_size ws <= size_slot x.(gv)) ->
    get_var_kind pmap x = ok (Some vpk) ->
    check_vpk_word rmap x.(gv) vpk ofs ws = ok t ->
    exists sr bytes,
      [/\ check_gvalid rmap x = Some (sr, bytes),
      let isub_ofs := interval_of_zone (sub_zone_at_ofs sr.(sr_zone) ofs (wsize_size ws)) in
      ByteSet.mem bytes isub_ofs &
      is_align (sub_region_addr (sub_region_at_ofs sr ofs (wsize_size ws))) ws].
  Proof.
    move=> hofs hget.
    rewrite /check_vpk_word.
    t_xrbindP => sr' /(check_vpkP hofs hget) [sr [bytes [hgvalid -> hmem]]].
    assert (hwf := check_gvalid_wf wfr_wf hgvalid).
    change (wsize_size ws) with (size_of (sword ws)) in hofs.
    have hwf' := sub_region_at_ofs_wf hwf hofs.
    move=> /(check_alignP hwf') hal.
    by exists sr, bytes.
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

  Lemma addr_from_pkP (x:var_i) pk sr xi ofs :
    wf_local x pk ->
    valid_pk rmap s' sr pk ->
    addr_from_pk pmap x pk = ok (xi, ofs) ->
    exists w,
      get_var (evm s') xi >>= to_pointer = ok w /\
      sub_region_addr sr = (w + wrepr _ ofs)%R.
  Proof.
    case: pk => //.
    + move=> sl ofs' ws z sc hwfpk /= -> [<- <-].
      rewrite /= /get_gvar /= base_ptrP /= truncate_word_u.
      eexists; split; first by reflexivity.
      rewrite /sub_region_addr /=.
      by rewrite (wfd_offset hwfpk) wrepr_add GRing.addrA.
    move=> p hwfpk /= hpk [<- <-].
    rewrite /= /get_gvar /= hpk /= truncate_word_u.
    eexists; split; first by reflexivity.
    by rewrite wrepr0 GRing.addr0.
  Qed.

  (* If [x] is a local variable *)
  Lemma check_mk_addr_ptr (x:var_i) aa ws xi ei e1 i1 pk sr :
    sem_pexpr [::] s' e1 >>= to_int = ok i1 ->
    wf_local x pk ->
    valid_pk rmap s' sr pk ->
    mk_addr_ptr pmap x aa ws pk e1 = ok (xi, ei) ->
    ∃ (wx wi : u64),
      [/\ Let x := get_var (evm s') xi in to_pointer x = ok wx,
          Let x := sem_pexpr [::] s' ei in to_pointer x = ok wi
        & (sub_region_addr sr + wrepr U64 (i1 * mk_scale aa ws))%R = (wx + wi)%R].
  Proof.
    move=> he1 hwfpk hpk.
    rewrite /mk_addr_ptr.
    t_xrbindP=> -[xi' ofs] haddr <- <-.
    move: haddr => /(addr_from_pkP hwfpk hpk) [wx [-> ->]].
    rewrite (mk_ofsP _ _ _ he1) /= truncate_word_u.
    eexists _, _; split=> //.
    by rewrite Z.add_comm wrepr_add GRing.addrA.
  Qed.

  (* TODO: move this *)
  Lemma arr_is_align p ws : WArray.is_align p ws -> is_align (wrepr _ p) ws.
  Proof.
    move=> /eqP h1; apply is_align_mod.
    by rewrite wunsigned_repr -/(wbase Uptr) (cut_wbase_Uptr ws) Z.mul_comm mod_pq_mod_q.
  Qed.

  Definition valid_vpk rv s2 x sr vpk :=
    match vpk with
    | VKglob (_, ws) => sr = sub_region_glob x ws
    | VKptr pk => valid_pk rv s2 sr pk
    end.

  (* A variant of [wfr_PTR] for [gvar]. *)
  (* Is it useful? *)
  Lemma wfr_gptr x sr bytes :
    check_gvalid rmap x = Some (sr, bytes) ->
    exists vpk, get_var_kind pmap x = ok (Some vpk)
    /\ valid_vpk rmap s' x.(gv) sr vpk.
  Proof.
    rewrite /check_gvalid /get_var_kind.
    case: is_glob.
    + case heq: Mvar.get => [[ofs ws]|//] /= [<- _].
      have /get_globalP -> := heq.
      by eexists.
    case heq: Mvar.get => // [sr'] [<- _].
    have /wfr_ptr [pk [-> hpk]] := heq.
    by eexists.
  Qed.

  (* [wf_global] and [wf_direct] in a single predicate. *)
  Definition wf_vpk x vpk :=
    match vpk with
    | VKglob zws => wf_global x zws.1 zws.2
    | VKptr pk => wf_local x pk
    end.

  Lemma get_var_kind_wf x vpk :
    get_var_kind pmap x = ok (Some vpk) ->
    wf_vpk x.(gv) vpk.
  Proof.
    rewrite /get_var_kind.
    case: is_glob.
    + by t_xrbindP=> -[ofs ws] /get_globalP /wf_globals ? <-.
    case heq: get_local => [pk|//] [<-].
    by apply wf_locals.
  Qed.

  Lemma addr_from_vpkP (x:var_i) vpk sr xi ofs :
    wf_vpk x vpk ->
    valid_vpk rmap s' x sr vpk ->
    addr_from_vpk pmap x vpk = ok (xi, ofs) ->
    exists w,
      get_var (evm s') xi >>= to_pointer = ok w /\
      sub_region_addr sr = (w + wrepr _ ofs)%R.
  Proof.
    case: vpk => [[ofs' ws]|pk].
    + move=> hwfpk /= -> [<- <-].
      rewrite /= /get_gvar /= vs_rip /= truncate_word_u.
      eexists; split; first by reflexivity.
      rewrite /sub_region_addr /=.
      by rewrite (wfg_offset hwfpk) wrepr0 GRing.addr0.
    by apply addr_from_pkP.
  Qed.

  Lemma check_mk_addr (x:var_i) aa ws xi ei e1 i1 vpk sr :
    sem_pexpr [::] s' e1 >>= to_int = ok i1 ->
    wf_vpk x vpk ->
    valid_vpk rmap s' x sr vpk ->
    mk_addr pmap x aa ws vpk e1 = ok (xi, ei) ->
    ∃ (wx wi : u64),
      [/\ Let x := get_var (evm s') xi in to_pointer x = ok wx,
          Let x := sem_pexpr [::] s' ei in to_pointer x = ok wi
        & (sub_region_addr sr + wrepr U64 (i1 * mk_scale aa ws))%R = (wx + wi)%R].
  Proof.
    move=> he1 hwfpk hpk.
    rewrite /mk_addr.
    t_xrbindP=> -[xi' ofs] haddr <- <-.
    move: haddr => /(addr_from_vpkP hwfpk hpk) [wx [-> ->]].
    rewrite (mk_ofsP _ _ _ he1) /= truncate_word_u.
    eexists _, _; split=> //.
    by rewrite Z.add_comm wrepr_add GRing.addrA.
  Qed.
(*
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
    + change (wsize_size ws) with (size_of (sword ws)) in hofs'.
      move /(check_alignP (sub_region_at_ofs_wf hwf hofs')) : halign.
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
*)
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
  Abort.

  Lemma sub_region_addr_offset len sr ofs :
    (sub_region_addr sr + wrepr _ ofs)%R =
    sub_region_addr (sub_region_at_ofs sr (Some ofs) len).
  Proof. by rewrite /sub_region_addr wrepr_add GRing.addrA. Qed.

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

  Lemma valid_pointer_sub_region_addr sr ws :
    wf_sub_region sr (sword ws) ->
    is_align (sub_region_addr sr) ws ->
    valid_pointer (emem s') (sub_region_addr sr) ws.
  Proof.
    move=> hwf hal.
    have hptr := vs_slot_valid (valid_state:=hvalid) hwf.(wfr_slot).
    apply /Memory.valid_pointerP; split=> //.
    move=> k hk; apply hptr; move: hk.
    apply between_byte.
    + by apply (no_overflow_sub_region_addr hwf).
    apply (zbetween_sub_region_addr hwf).
  Qed.

  Lemma valid_pointer_sub_region_at_ofs sr ty ofs ws :
    wf_sub_region sr ty ->
    0 <= ofs /\ ofs + wsize_size ws <= size_of ty ->
    is_align (sub_region_addr sr + wrepr _ ofs) ws ->
    valid_pointer (emem s') (sub_region_addr sr + wrepr _ ofs)%R ws.
  Proof.
    move=> hwf hbound.
    have hofs: forall zofs : Z, Some ofs = Some zofs ->
      0 <= zofs /\ zofs + size_of (sword ws) <= size_of ty.
    + by move=> _ [<-].
    have hwf' := sub_region_at_ofs_wf hwf hofs.
    rewrite (sub_region_addr_offset (wsize_size ws)).
    by apply (valid_pointer_sub_region_addr hwf').
  Qed.

  Lemma memi_mem_U8 bytes z off :
    ByteSet.memi bytes (z.(z_ofs) + off) =
    ByteSet.mem bytes (interval_of_zone (sub_zone_at_ofs z (Some off) (wsize_size U8))).
  Proof.
    apply /idP/idP.
    + move=> hmem; apply /ByteSet.memP; move=> i.
      rewrite /interval_of_zone /I.memi /= wsize8 !zify => hbound.
      by have -> : i = z_ofs z + off by lia.
    move=> /ByteSet.memP; apply.
    by rewrite /interval_of_zone /I.memi /= wsize8 !zify; lia.
  Qed.

  Lemma sub_zone_at_ofs_compose z ofs1 ofs2 len1 len2 :
    sub_zone_at_ofs (sub_zone_at_ofs z (Some ofs1) len1) (Some ofs2) len2 =
    sub_zone_at_ofs z (Some (ofs1 + ofs2)) len2.
  Proof. by rewrite /= Z.add_assoc. Qed.

  (* On the model of [between_byte]. *)
  Lemma zbetween_zone_byte z1 z2 i :
    zbetween_zone z1 z2 ->
    0 <= i /\ i < z2.(z_len) ->
    zbetween_zone z1 (sub_zone_at_ofs z2 (Some i) (wsize_size U8)).
  Proof. by rewrite /zbetween_zone wsize8 !zify /=; lia. Qed.

  Lemma zbetween_zone_sub_zone_at_ofs_option z i ofs len ty sl :
    wf_zone z ty sl ->
    0 <= i /\ i + len <= size_of ty ->
    (ofs <> None -> ofs = Some i) ->
    zbetween_zone (sub_zone_at_ofs z ofs len) (sub_zone_at_ofs z (Some i) len).
  Proof.
    move=> hwf hi.
    case: ofs => [ofs|].
    + by move=> /(_ ltac:(discriminate)) [->]; apply zbetween_zone_refl.
    move=> _.
    apply (zbetween_zone_sub_zone_at_ofs hwf).
    by move=> _ [<-].
  Qed.

(*
  Lemma get_read_mem (* v *) sr bytes ws w :
    wf_sub_region sr (sword ws) ->
    eq_sub_region_val (emem s') sr bytes (Vword w) ->
    ByteSet.mem bytes (interval_of_zone sr.(sr_zone)) ->
(*     get_val ws v 0 = ok w -> *)
    is_align (sub_region_addr sr) ws ->
    read_mem (emem s') (sub_region_addr sr) ws = ok w.
  Proof.
  Admitted.
*)
(* TODO: relire cette preuve pour voir si les hypothèses sont indispensables
   et les plus logiques.
   On voudrait ne pas utiliser lia !
   Peut-on faire un premier lemme sans ofs, juste pour les Vword ws ?
   Et ensuite un 2ème lemme qui parle de n'importe quel sr dont on prend
   ws ? (cf valid_pointer_sub_region_addr et valid_pointer_sub_region_at_ofs)

   Intuition du lemme : eq_sub_region_val donne correspondance entre lire
   dans v et lire dans la mémoire, mais seulement pour des bytes.
   On montre que c'est aussi vrai pour n'importe quelle taille [ws] de lecture.
*)
  Lemma get_val_read_mem (v : value) sr bytes ofs ws aa i w :
    wf_sub_region sr (type_of_val v) ->
    eq_sub_region_val_read (emem s') sr bytes v ->
    ByteSet.mem bytes (interval_of_zone (sub_zone_at_ofs sr.(sr_zone) ofs (wsize_size ws))) ->
    (ofs <> None -> ofs = Some (i * mk_scale aa ws)) ->
    get_val aa ws v i = ok w ->
    is_align (sub_region_addr sr + wrepr _ (i * mk_scale aa ws)) ws ->
    read_mem (emem s') (sub_region_addr sr + wrepr _ (i * mk_scale aa ws)) ws = ok w.
  Proof.
    move=> hwf heq hmem hofs.
    rewrite /get_val; t_xrbindP=> a ha hget hal.
    rewrite Memory.readP /CoreMem.read.
    have /= := WArray.get_bound hget.
    rewrite Z2Pos.id; last by apply size_of_gt0.
    move=> [hbound1 hbound2 _].
    have := valid_pointer_sub_region_at_ofs hwf (conj hbound1 hbound2) hal.
    rewrite -validr_valid_pointer => /is_okP [_] -> /=.
    move: (hget); rewrite /WArray.get /CoreMem.read; t_xrbindP => _ _ <-.
    do 2 f_equal; rewrite /CoreMem.uread.
    apply eq_map_ziota => k /= hk.
    have [v' hget8]:= WArray.get_get8 AAscale hget hk.
    rewrite (WArray.get_uget hget8).
    have: get_val_byte v (i * mk_scale aa ws + k) = ok v'.
    + by rewrite /get_val_byte /get_val ha.
    move /heq; rewrite Memory.readP /CoreMem.read.
    have h: ByteSet.memi bytes (sr.(sr_zone).(z_ofs) + (i * mk_scale aa ws + k)).
    + rewrite memi_mem_U8; apply: subset_mem hmem; rewrite subset_interval_of_zone.
      rewrite -(sub_zone_at_ofs_compose _ _ _ (wsize_size ws)).
      apply: zbetween_zone_byte => //.
      by apply (zbetween_zone_sub_zone_at_ofs_option hwf).
    move=> /(_ h){h}; t_xrbindP => _ _.
    by rewrite CoreMem.uread8_get addE wrepr_add GRing.addrA.
  Qed.
(*
  Lemma get_arr_read_mem (n:positive) (t : WArray.array n) sr bytes ofs aa ws i w :
    wf_sub_region sr (sarr n) ->
    eq_sub_region_val (sarr n) (emem s') sr bytes (Varr t) ->
    ByteSet.mem bytes (interval_of_zone (sub_zone_at_ofs sr.(sr_zone) ofs (wsize_size ws))) ->
    (ofs <> None -> ofs = Some (i * mk_scale aa ws)) ->
    WArray.get aa ws t i = ok w ->
    is_align (sub_region_addr sr + wrepr U64 (i * mk_scale aa ws)) ws ->
    read_mem (emem s') (sub_region_addr sr + wrepr U64 (i * mk_scale aa ws)) ws = ok w.
  Proof.
    move=> hwf heq (* hgvalid *) hmem hofs hget hal.
    rewrite Memory.readP /CoreMem.read.
    have [hbound1 hbound2 _] := WArray.get_bound hget.
    have := valid_pointer_sub_region_at_ofs hwf (conj hbound1 hbound2) hal.
    rewrite -validr_valid_pointer => /is_okP [?] /= => hv; rewrite hv /=.
    move: (hget);rewrite /WArray.get /CoreMem.read; t_xrbindP => ? _ <-.
    do 2 f_equal; rewrite /CoreMem.uread.
    apply eq_map_ziota => k hk /=.
    have [v hget8]:= WArray.get_get8 AAscale hget hk.
    have /WArray.get_uget -> := hget8.
    move /heq: hget8; rewrite Memory.readP /CoreMem.read.
    have h: 0 <= i * mk_scale aa ws + k ∧ i * mk_scale aa ws + k < n by lia.
    have h1: ByteSet.memi bytes (sr.(sr_zone).(z_ofs) + (i * mk_scale aa ws + k)).
    + move /ByteSet.memP : hmem; apply.
      rewrite /I.memi /= !zify.
      case: ofs hofs => [ofs|_].
      + by move=> /(_ ltac:(discriminate)) [->] /=; lia.
      by have /= hlen := hwf.(wfz_len); lia.
    move=> /(_ h h1){h h1}; t_xrbindP => ? hvr.
    by rewrite CoreMem.uread8_get addE wrepr_add GRing.addrA.
  Qed.

  Lemma get_word_read_mem ws (w : word ws) sr bytes:
    wf_sub_region sr (sword ws) ->
    eq_sub_region_val (sword ws) (emem s') sr bytes (Vword w) ->
    ByteSet.mem bytes (interval_of_zone (sub_zone_at_ofs sr.(sr_zone) (Some 0)%Z (wsize_size ws))) ->
    is_align (sub_region_addr sr) ws ->
    read_mem (emem s') (sub_region_addr sr) ws = ok w.
  Proof.
    move=> hwf heq hmem hal.
    have [t ht] : exists t, WArray.set (WArray.empty (Z.to_pos (wsize_size ws))) AAscale 0 w = ok t.
    + rewrite /WArray.set CoreMem.write_uwrite; first by eexists; reflexivity.
      change (validw (WArray.empty (Z.to_pos (wsize_size ws))) (0 * mk_scale AAscale ws) ws)
        with (WArray.validw (WArray.empty (Z.to_pos (wsize_size ws))) (0 * mk_scale AAscale ws) ws).
      by rewrite /WArray.validw /WArray.in_range /= Z.leb_refl.
    have hwf': wf_sub_region sr (sarr (Z.to_pos (wsize_size ws))).
    + by case: hwf => ? [*]; split.
    have heq': eq_sub_region_val (sarr (Z.to_pos (wsize_size ws))) (emem s') sr bytes (Varr t).
    + move=> off hoff hmem' w' hval.
      apply heq => //.
      by rewrite /get_val_byte /get_val /array_of_val ht.
    have := get_arr_read_mem (t := t) (sr:=sr) hwf' heq' hmem _ (WArray.setP_eq ht).
    rewrite /= wrepr0 GRing.addr0.
    by apply.
  Qed.
*)
  Lemma size_of_subtype ty1 ty2 :
    subtype ty1 ty2 ->
    size_of ty1 <= size_of ty2.
  Proof.
    case: ty1 ; case: ty2 => //=.
    + by move=> ??; apply Z.leb_le.
    by move=> [] [].
  Qed.

  Lemma wf_sub_region_subtype sr ty1 ty2 :
    subtype ty2 ty1 ->
    wf_sub_region sr ty1 ->
    wf_sub_region sr ty2.
  Proof.
    move=> hsub [hwf1 [hwf2 hwf3]]; split=> //; split=> //.
    by move /size_of_subtype : hsub; lia.
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

(* [type_of_get_var] is not precise enough. We need the fact that [v] is
   necessarily of the form [Vword w] (i.e. is not [Vundef]).
*)
Lemma get_gvar_word x ws gd vm v :
  x.(gv).(vtype) = sword ws ->
  get_gvar gd vm x = ok v ->
  exists (ws' : wsize) (w : word ws'), (ws' <= ws)%CMP /\ v = Vword w.
Proof.
  move=> hty; rewrite /get_gvar.
  case: (is_lvar x).
  + rewrite /get_var; apply : on_vuP => // t _ <-.
    move: t; rewrite hty => t /=.
    by eexists _, _; split; first by apply pw_proof.
  move=> /get_globalI [gv [_]]; rewrite hty.
  case: gv => ?? -> // [<-].
  by eexists _, _; split.
Qed.

(* [psem.type_of_val_word] could be much more precise. *)
Lemma type_of_val_word :
∀ (v : value) (wz : wsize),
  type_of_val v = sword wz
  → (wz = U8 /\ exists wz', v = Vundef wz') ∨ (∃ w : word wz, v = Vword w).
Proof.
  move=> v wz.
  case: v => //=.
  + move=> wz' w [?]; subst wz'. right. eauto.
  move=> [] //= wz' [<-]. left. split=> //. eauto.
Qed.

(* If we read a large enough sub-word, we get the full word. *)
Lemma get_val_word aa ws w :
  get_val aa ws (Vword w) 0 = ok w.
Proof.
  rewrite /get_val /array_of_val.
  set empty := WArray.empty _.
  have [t ht] : exists t, WArray.set empty AAscale 0 w = ok t.
    + rewrite /WArray.set CoreMem.write_uwrite; first by eexists; reflexivity.
      by rewrite /= /WArray.validw /WArray.in_range /= Z.leb_refl.
  rewrite ht /=.
  by apply (WArray.setP_eq ht).
Qed.

Lemma get_val_array n aa ws (a : WArray.array n) i :
  get_val aa ws (Varr a) i = WArray.get aa ws a i.
Proof. by []. Qed.

Lemma sub_region_at_ofs_None sr len :
  sub_region_at_ofs sr None len = sr.
Proof. by case: sr. Qed.

Lemma check_diffP x t : check_diff pmap x = ok t -> ~Sv.In x (vnew pmap).
Proof. by rewrite /check_diff; case:ifPn => /Sv_memP. Qed.

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
      + by t_xrbindP=> _ /check_diffP hnnew <-; apply: get_var_kindP.
      case hty: is_word_type => [ws | //]; move /is_word_typeP in hty.
      t_xrbindP => ? hcheck [xi ei] haddr <- hget /=.
      have h0: Let x := sem_pexpr [::] s' 0 in to_int x = ok 0 by done.
      have h1: forall zofs, Some 0 = Some zofs -> 0 <= zofs /\ zofs + wsize_size ws <= size_slot x.(gv).
      + by move=> _ [<-]; rewrite hty /=; lia.
      have [sr [bytes [hgvalid hmem halign]]] := check_vpk_wordP h1 hgvk hcheck.
      have h2: valid_vpk rmap s' x.(gv) sr vpk.
      + have := wfr_gptr hgvalid.
        by rewrite hgvk => -[_ [[]] <-].
      have [wx [wi [-> -> /= haddr2]]] := check_mk_addr h0 (get_var_kind_wf hgvk) h2 haddr.
      rewrite -haddr2.
      rewrite -sub_region_addr_offset in halign.
      assert (heq := wfr_val hgvalid hget); rewrite hty in heq.
      case: heq => hread hval.
      assert (hwf := check_gvalid_wf wfr_wf hgvalid).
      rewrite hty -hval in hwf.
      have [ws' [w [_ ?]]] := get_gvar_word hty hget; subst v.
      case: hval => ?; subst ws'.
      have h3: Some 0 ≠ None → Some 0 = Some (0 * mk_scale AAdirect ws) by done.
      by rewrite (get_val_read_mem hwf hread hmem h3 (get_val_word _ w) halign).
    + move=> aa sz x e1 he1 e' v he'; apply: on_arr_gvarP => n t hty /= hget.
      t_xrbindP => i vi /he1{he1}he1 hvi w hw <-.
      move: he'; t_xrbindP => e1' /he1{he1}he1'.
      have h0 : sem_pexpr [::] s' e1' >>= to_int = ok i.
      + by rewrite he1'.
      move=> [vpk | ]; last first.
      + t_xrbindP => h _ /check_diffP h1 <- /=.
        by rewrite (get_var_kindP h h1 hget) /= h0 /= hw.
      t_xrbindP => hgvk ? hcheck [xi ei] haddr <- /=.
      have [h1 h2 h3] := WArray.get_bound hw.
      have h4 : forall zofs, mk_ofsi aa sz e1' = Some zofs ->
        0 <= zofs /\ zofs + wsize_size sz <= size_slot x.(gv).
      + move=> zofs heq.
        have := mk_ofsiP h0 (aa:=aa) (sz:=sz).
        by rewrite heq => /(_ ltac:(discriminate)) [->] /=; rewrite hty.
      have [sr [bytes [hgvalid hmem halign]]] := check_vpk_wordP h4 hgvk hcheck.
      have h5: valid_vpk rmap s' x.(gv) sr vpk.
      + have := wfr_gptr hgvalid.
        by rewrite hgvk => -[_ [[]] <-].
      have [wx [wi [-> -> /= haddr2]]] := check_mk_addr h0 (get_var_kind_wf hgvk) h5 haddr.
      rewrite -haddr2.
      have h6: is_align (sub_region_addr sr + wrepr _ (i * mk_scale aa sz)) sz.
      + case: mk_ofsi (mk_ofsiP h0 (aa:=aa) (sz:=sz)) halign.
        + move=> _ /(_ ltac:(discriminate)) [->].
          by rewrite -sub_region_addr_offset.
        move=> _.
        rewrite sub_region_at_ofs_None => halign2.
        apply is_align_add => //.
        by apply arr_is_align.
      assert (heq := wfr_val hgvalid hget).
      case: heq => hread _.
      assert (hwf := check_gvalid_wf wfr_wf hgvalid).
      rewrite hty in hwf; change (sarr n) with (type_of_val (Varr t)) in hwf.
      rewrite -get_val_array in hw.
      by rewrite (get_val_read_mem hwf hread hmem (mk_ofsiP h0) hw h6).
    + move=> sz1 v1 e1 IH e2 v.
      t_xrbindP => _ /check_varP hc _ /check_diffP hnnew e1' /IH hrec <- wv1 vv1 /= hget hto' we1 ve1.
      move=> /hrec -> hto wr hr ?; subst v.
      have := get_var_kindP hc hnnew hget; rewrite /get_gvar /= => -> /=.
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
  case: s1 s2 => mem1 vm1 [mem2 vm2] [/=] hvalid hdisj hincl hunch hrip hrsp heqvm hwfr heqmem hget hnin.
  constructor => //=.
  + by rewrite get_var_neq //; assert (h:=rip_in_new); SvD.fsetdec.
  + by rewrite get_var_neq //; assert (h:=rsp_in_new); SvD.fsetdec.
  + by move=> y hy hnnew; apply get_var_set_eq; apply heqvm.
  rewrite /with_vm /=; case: hwfr => hwfsr hval hptr.
  constructor => //.
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

Lemma disjoint_zrange_byte p1 sz1 p2 sz2 i :
  disjoint_zrange p1 sz1 p2 sz2 ->
  0 <= i /\ i < sz2 ->
  disjoint_zrange p1 sz1 (p2 + wrepr _ i) (wsize_size U8).
Proof.
  move=> hd hrange.
  case: (hd) => _ hover _.
  apply: disjoint_zrange_incl_r hd.
  apply: (between_byte hover) => //.
  by apply zbetween_refl.
Qed.

Lemma get_val_byte_bound v off w :
  get_val_byte v off = ok w -> 0 <= off /\ off < size_val v.
Proof.
  rewrite /get_val_byte /get_val.
  t_xrbindP=> a harray /WArray.get_bound /= [].
  rewrite Z.mul_1_r wsize8 Z2Pos.id; last by apply size_of_gt0.
  by lia.
Qed.

Lemma eq_sub_region_val_disjoint_zrange sr bytes ty mem1 mem2 v p sz :
  (forall p1 ws1,
    disjoint_zrange p sz p1 (wsize_size ws1) ->
    read_mem mem2 p1 ws1 = read_mem mem1 p1 ws1) ->
  disjoint_zrange p sz (sub_region_addr sr) (size_of ty) ->
  eq_sub_region_val ty mem1 sr bytes v ->
  eq_sub_region_val ty mem2 sr bytes v.
Proof.
  move=> hreadeq hd [hread hty]; split=> // off hmem w' hget.
  rewrite -(hread _ hmem _ hget).
  apply hreadeq.
  apply (disjoint_zrange_byte hd).
  rewrite -hty.
  by apply (get_val_byte_bound hget).
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

Lemma wf_region_slot_inj r1 r2 :
  wf_region r1 -> wf_region r2 ->
  r1.(r_slot) = r2.(r_slot) ->
  r1 = r2.
Proof.
  move=> hwf1 hwf2.
  have := hwf1.(wfr_align).
  have := hwf2.(wfr_align).
  have := hwf1.(wfr_writable).
  have := hwf2.(wfr_writable).
  by case: (r1); case: (r2) => /=; congruence.
Qed.

Lemma eq_sub_region_val_disjoint_regions s2 sr ty sry ty' mem2 bytes v :
  wf_sub_region sr ty ->
  wf_sub_region sry ty' ->
  sr.(sr_region) <> sry.(sr_region) ->
  sr.(sr_region).(r_writable) ->
  (forall p ws,
    disjoint_zrange (sub_region_addr sr) (size_of ty) p (wsize_size ws) ->
    read_mem mem2 p ws = read_mem (emem s2) p ws) ->
  eq_sub_region_val ty' (emem s2) sry bytes v ->
  eq_sub_region_val ty' mem2 sry bytes v.
Proof.
  move=> hwf hwfy hneq hw hreadeq.
  apply (eq_sub_region_val_disjoint_zrange hreadeq).
  apply (disjoint_zrange_incl (zbetween_sub_region_addr hwf) (zbetween_sub_region_addr hwfy)).
  apply (disjoint_writable hwf.(wfr_slot) hwfy.(wfr_slot)); last by rewrite hwf.(wfr_writable).
  by move=> /(wf_region_slot_inj hwf hwfy).
Qed.

Lemma disjoint_zones_disjoint_zrange sr1 ty1 sr2 ty2 :
  wf_sub_region sr1 ty1 ->
  wf_sub_region sr2 ty2 ->
  sr1.(sr_region) = sr2.(sr_region) ->
  disjoint_zones (sub_zone_at_ofs sr1.(sr_zone) (Some 0) (size_of ty1))
                 (sub_zone_at_ofs sr2.(sr_zone) (Some 0) (size_of ty2)) ->
  disjoint_zrange (sub_region_addr sr1) (size_of ty1) (sub_region_addr sr2) (size_of ty2).
Proof.
  move=> hwf1 hwf2 heq.
  have := addr_no_overflow (wfr_slot hwf1).
  have := addr_no_overflow (wfr_slot hwf2).
  rewrite /disjoint_zones /disjoint_range /disjoint_zrange /no_overflow !Zcmp_le !zify /=.
  rewrite (wunsigned_sub_region_addr hwf1) (wunsigned_sub_region_addr hwf2).
  have /= := wfz_len hwf1.
  have /= := wfz_len hwf2.
  have := wfz_ofs hwf1.
  have := wfz_ofs hwf2.
  rewrite heq.
  by split; rewrite ?zify; lia.
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

(* devrait-on remplacer les deux hypothèses par des wf_zone ? *)
Lemma disjoint_interval_of_zone z1 z2 :
  0 < z1.(z_len) -> 0 < z2.(z_len) ->
  disjoint_intervals (interval_of_zone z1) (interval_of_zone z2) =
  disjoint_zones z1 z2.
Proof.
  move=> hlen1 hlen2.
  rewrite /disjoint_intervals /interval_of_zone /disjoint_zones /I.is_empty /=.
  by apply /idP/idP; rewrite !Zcmp_le !zify; lia.
Qed.

Lemma eq_sub_region_val_same_region s2 sr ty sry ty' mem2 bytes v :
  wf_sub_region sr ty ->
  wf_sub_region sry ty' ->
  sr.(sr_region) = sry.(sr_region) ->
  (forall p ws,
    disjoint_zrange (sub_region_addr sr) (size_of ty) p (wsize_size ws) ->
    read_mem mem2 p ws = read_mem (emem s2) p ws) ->
  eq_sub_region_val ty' (emem s2) sry bytes v ->
  eq_sub_region_val ty' mem2 sry (ByteSet.remove bytes (interval_of_zone sr.(sr_zone))) v.
Proof.
  move=> hwf hwfy hr hreadeq [hread hty'].
  split=> // off; rewrite memi_mem_U8 => /mem_remove [hmem hdisj] v1 hget.
  rewrite -(hread _ _ _ hget); last by rewrite memi_mem_U8.
  apply hreadeq.
  rewrite (sub_region_addr_offset (wsize_size U8)).
  have hwfy': wf_sub_region (sub_region_at_ofs sry (Some off) (wsize_size U8)) sword8.
  + change (wsize_size U8) with (size_of sword8).
    apply: (sub_region_at_ofs_wf hwfy).
    move=> _ [<-]; rewrite /= wsize8 -hty'.
    by have := get_val_byte_bound hget; lia.
  apply (disjoint_zones_disjoint_zrange hwf hwfy' hr).
  rewrite (disjoint_interval_of_zone (wf_zone_len_gt0 hwf)) // in hdisj.
  by apply (disjoint_zones_incl (zbetween_zone_sub_zone_at_ofs_0 hwf)
                                (zbetween_zone_sub_zone_at_ofs_0 hwfy')).
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
Lemma get_var_bytes_set_pure_bytes rmap x sr ofs len r y :
  get_var_bytes (set_pure_bytes rmap x sr ofs len) r y =
    let bytes := get_var_bytes rmap r y in
    if sr.(sr_region) != r then
      bytes
    else
      let i := interval_of_zone (sub_zone_at_ofs sr.(sr_zone) ofs len) in
      if x == y then
        if ofs is None then
          bytes
        else
          ByteSet.add i bytes
      else
        ByteSet.remove bytes i.
Proof.
  rewrite /set_pure_bytes /get_var_bytes /=.
  rewrite get_bytes_map_setP.
  case: eqP => [->|] //=.
  rewrite get_bytes_setP.
  by case: eqP => [->|] // _; rewrite get_bytes_clear.
Qed.

Lemma set_bytesP rmap x sr ofs len rv :
  set_bytes rmap x sr ofs len = ok rv ->
  sr.(sr_region).(r_writable) /\ rv = set_pure_bytes rmap x sr ofs len.
Proof. by rewrite /set_bytes; t_xrbindP=> _ /assertP. Qed.

Lemma set_sub_regionP rmap x sr ofs len rmap2 :
  set_sub_region rmap x sr ofs len = ok rmap2 ->
  sr.(sr_region).(r_writable) /\
  rmap2 = {| var_region := Mvar.set (var_region rmap) x sr;
             region_var := set_pure_bytes rmap x sr ofs len |}.
Proof. by rewrite /set_sub_region; t_xrbindP=> _ /set_bytesP [? ->] <-. Qed.

(*
Definition get_gvar_bytes rv r x :=
  if is_glob x then
    ByteSet.full (interval_of_zone {| z_ofs := 0; z_len := size_slot x.(gv) |})
  else get_var_bytes rv r x.(gv).
*)

Lemma check_gvalid_set_sub_region rmap x sr ofs len rmap2 y sry bytes :
  wf_sub_region sr x.(vtype) ->
  set_sub_region rmap x sr ofs len = ok rmap2 ->
  check_gvalid rmap2 y = Some (sry, bytes) ->
    [/\ ~ is_glob y, x = gv y, sr = sry &
         bytes = get_var_bytes rmap2 sr.(sr_region) x]
  \/
    [/\ ~ is_glob y -> x <> gv y &
        exists bytes', check_gvalid rmap y = Some (sry, bytes') /\
          bytes =
            if sr.(sr_region) != sry.(sr_region) then bytes'
            else ByteSet.remove bytes' (interval_of_zone (sub_zone_at_ofs sr.(sr_zone) ofs len))].
(*               get_gvar_bytes (set_sub_region rmap x sr) sry.(sr_region) y]. *)
Proof.
  move=> hwf /set_sub_regionP [hw ->]; rewrite /check_gvalid.
  case: (@idP (is_glob y)) => hg.
  + case heq: Mvar.get => [[ofs' ws]|//] [<- <-].
    right; split => //.
    eexists; split; first by reflexivity.
    case: eqP => heqr //=.
    by rewrite -hwf.(wfr_writable) heqr (sub_region_glob_wf (wf_globals heq)).(wfr_writable) in hw.
  rewrite Mvar.setP; case: eqP.
  + by move=> -> [<- <-]; left; split.
  move=> hneq.
  case heq': Mvar.get => [sr'|//] [? <-]; subst sr'.
  right; split => //.
  eexists; split; first by reflexivity.
  rewrite get_var_bytes_set_pure_bytes.
  by move: hneq => /eqP /negPf ->.
Qed.

Definition between_at_ofs sr ty ofs ty2 p ws :=
  between (sub_region_addr (sub_region_at_ofs sr ofs (size_of ty2)))
          (size_of (stype_at_ofs ofs ty2 ty))
          p ws.

(* This lemma is used for [set_sub_region] and [set_stack_ptr]. *)
Lemma mem_unchanged_write_slot m0 s1 s2 sr ty mem2 :
  wf_sub_region sr ty ->
  sr.(sr_region).(r_writable) ->
  (forall p ws,
    disjoint_zrange (sub_region_addr sr) (size_of ty) p (wsize_size ws) ->
    read_mem mem2 p ws = read_mem (emem s2) p ws) ->
  mem_unchanged (emem s1) m0 (emem s2) ->
  mem_unchanged (emem s1) m0 mem2.
Proof.
  move=> hwf hwritable hreadeq hunch p hvalid1 hvalid2 hdisj.
  rewrite (hunch _ hvalid1 hvalid2 hdisj).
  symmetry; apply hreadeq.
  apply (disjoint_zrange_incl_l (zbetween_sub_region_addr hwf)).
  apply (hdisj _ hwf.(wfr_slot)).
  by rewrite hwf.(wfr_writable).
Qed.

(*
Lemma disjoint_writable_is_constant_set_sub_region rmap m0 s1 s2 sr x ofs ty p ws w mem2 rmap2 :
  wf_sub_region sr x.(vtype) ->
  (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + size_of ty <= size_of x.(vtype)) ->
  between_at_ofs sr x.(vtype) ofs ty p ws ->
  write_mem (emem s2) p ws w = ok mem2 ->
  set_sub_region rmap x sr ofs (size_of ty) = ok rmap2 ->
  disjoint_writable_is_constant (emem s1) m0 (emem s2) ->
  disjoint_writable_is_constant (emem s1) m0 mem2.
Proof.
  move=> hwf hofs hb hmem2 hset hunch p' hvalid1 hvalid2 hdisj.
  rewrite (hunch _ hvalid1 hvalid2 hdisj).
  symmetry; apply (Memory.writeP_neq hmem2).
  move: hset => /set_sub_regionP [hwritable _].
  have := hdisj _ hwf.(wfr_slot).
  rewrite hwf.(wfr_writable)=> /(_ hwritable).
  apply: disjoint_zrange_incl_l.
  apply: zbetween_trans hb.
  by apply (zbetween_sub_region_addr (sub_region_at_ofs_wf hwf hofs)).
Qed.*)

(* I tried to avoid proof duplication with this auxiliary lemma. But there is
   some duplication even in the proof of this lemma...
*)
Lemma valid_pk_set_pure_bytes rmap s2 x sr ofs ty mem2 y pk sry :
  wf_sub_region sr x.(vtype) ->
  ~ Sv.In x pmap.(vnew) ->
  (forall p ws,
    disjoint_zrange (sub_region_addr (sub_region_at_ofs sr ofs (size_of ty)))
                    (size_of (stype_at_ofs ofs ty x.(vtype)))
                    p (wsize_size ws) ->
    read_mem mem2 p ws = read_mem (emem s2) p ws) ->
  wf_local y pk ->
  (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + size_of ty <= size_of x.(vtype)) ->
  valid_pk rmap s2 sry pk ->
  valid_pk (set_pure_bytes rmap x sr ofs (size_of ty)) (with_mem s2 mem2) sry pk.
Proof.
  move=> hwf hnin hreadeq hlocal hofs hpk.
  case: pk hlocal hofs hpk => //= s ofs' ws' z f hlocal hofs hpk.
  have hwf' := sub_region_at_ofs_wf hwf hofs.
  have hwf2 := sub_region_stkptr_wf hlocal.
  rewrite /check_stack_ptr get_var_bytes_set_pure_bytes.
  case: eqP => heqr /=.
  + case: eqP => heq2.
    + by have := hlocal.(wfs_new); congruence.
    move=> /mem_remove [] /hpk <-.
    rewrite (disjoint_interval_of_zone (wf_zone_len_gt0 hwf')) // => hdisj.
    apply hreadeq.
    apply (disjoint_zones_disjoint_zrange hwf' hwf2 heqr).
    apply: disjoint_zones_incl_l hdisj.
    by apply (zbetween_zone_sub_zone_at_ofs_0 hwf').
  move=> /hpk <-.
  apply hreadeq.
  apply (disjoint_zrange_incl (zbetween_sub_region_addr hwf') (zbetween_sub_region_addr hwf2)).
  apply disjoint_zrange_sym.
  apply (disjoint_writable hwf2.(wfr_slot) hwf.(wfr_slot)); last by rewrite hwf2.(wfr_writable).
  by move=> /(wf_region_slot_inj hwf2 hwf); congruence.
Qed.

Lemma wfr_PTR_set_sub_region (rmap : region_map) s2 x pk sr ofs ty mem2 rmap2 :
  get_local pmap x = Some pk ->
  wf_sub_region sr x.(vtype) ->
  valid_pk rmap s2 sr pk ->
  (forall p ws,
    disjoint_zrange (sub_region_addr (sub_region_at_ofs sr ofs (size_of ty)))
                    (size_of (stype_at_ofs ofs ty x.(vtype)))
                    p (wsize_size ws) ->
    read_mem mem2 p ws = read_mem (emem s2) p ws) ->
  (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + size_of ty <= size_of x.(vtype)) ->
  set_sub_region rmap x sr ofs (size_of ty) = ok rmap2 ->
  wfr_PTR rmap s2 ->
  wfr_PTR rmap2 (with_mem s2 mem2).
Proof.
  move=> hlx hwf hpk hreadeq hofs /set_sub_regionP [_ ->] hptr y sry.
  have /wf_vnew hnnew := hlx.
  rewrite Mvar.setP; case: eqP.
  + move=> <- [<-].
    exists pk; split=> //.
    by apply (valid_pk_set_pure_bytes hwf hnnew hreadeq (wf_locals hlx) hofs hpk).
  move=> _ /hptr {pk hlx hpk} [pk [hly hpk]].
  exists pk; split=> //.
  by apply (valid_pk_set_pure_bytes hwf hnnew hreadeq (wf_locals hly) hofs hpk).
Qed.

Lemma pto_val_pof_val v t :
  pof_val (type_of_val v) v = ok t ->
  pto_val t = v.
Proof.
  case: v t => /=.
  + by move=> ?? [->].
  + by move=> ?? [->].
  + move=> len a _ [<-].
    by rewrite /WArray.inject Z.ltb_irrefl; case: a.
  + by move=> ws w pw; rewrite sumbool_of_boolET => -[<-].
  by move=> [].
Qed.

Lemma check_gvalid_lvar rmap (x : var_i) sr :
  Mvar.get rmap.(var_region) x = Some sr ->
  check_gvalid rmap (mk_lvar x) = Some (sr, get_var_bytes rmap sr.(sr_region) x).
Proof. by rewrite /check_gvalid /= => ->. Qed.

Lemma wfr_VAL_set_sub_region rmap s1 s2 sr x ofs ty mem2 (rmap2 : region_map) v :
  wf_rmap rmap s1 s2 ->
  wf_sub_region sr x.(vtype) ->
  (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + size_of ty <= size_of x.(vtype)) ->
  (forall p ws,
    disjoint_zrange (sub_region_addr (sub_region_at_ofs sr ofs (size_of ty)))
                    (size_of (stype_at_ofs ofs ty x.(vtype)))
                    p (wsize_size ws) ->
    read_mem mem2 p ws = read_mem (emem s2) p ws) ->
  set_sub_region rmap x sr ofs (size_of ty) = ok rmap2 ->
  eq_sub_region_val x.(vtype) mem2 sr (get_var_bytes rmap2 sr.(sr_region) x) v ->
  wfr_VAL rmap2 (with_vm s1 (evm s1).[x <- pof_val (vtype x) v]) (with_mem s2 mem2).
Proof.
  move=> hwfr hwf hofs hreadeq hset hval y sry bytesy vy.
  move=> /(check_gvalid_set_sub_region hwf hset) [].
  + move=> [? ? <- ->]; subst x.
    have [_ hty] := hval.
    rewrite get_gvar_eq //.
    apply on_vuP => //; rewrite -hty.
    by move => ? hof hto; rewrite -hto (pto_val_pof_val hof) hty.
  move=> [? [bytes [hgvalid ->]]].
  rewrite get_gvar_neq => //; move=> /(wfr_val hgvalid).
  assert (hwfy := check_gvalid_wf wfr_wf hgvalid).
  have hwf' := sub_region_at_ofs_wf hwf hofs.
  case: eqP => heqr /=.
  + apply (eq_sub_region_val_same_region hwf' hwfy heqr hreadeq).
  apply: (eq_sub_region_val_disjoint_regions hwf' hwfy heqr _ hreadeq).
  by case /set_sub_regionP : hset.
Qed.

(* This lemma is used for [set_sub_region] and [set_stack_ptr]. *)
Lemma eq_mem_source_write_slot rmap m0 s1 s2 sr ty mem2:
  valid_state rmap m0 s1 s2 ->
  wf_sub_region sr ty ->
  (forall p ws,
    disjoint_zrange (sub_region_addr sr) (size_of ty) p (wsize_size ws) ->
    read_mem mem2 p ws = read_mem (emem s2) p ws) ->
  eq_mem_source (emem s1) mem2.
Proof.
  move=> hvs hwf hreadeq p ws hvp.
  rewrite (vs_eq_mem hvp).
  symmetry; apply hreadeq.
  apply (disjoint_zrange_incl_l (zbetween_sub_region_addr hwf)).
  by apply (vs_disjoint hwf.(wfr_slot) hvp).
Qed.

(*
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

Lemma set_wordP rmap m0 s1 s2 x sr ws rmap2 :
  valid_state rmap m0 s1 s2 ->
  wf_sub_region sr x.(vtype) ->
  set_word rmap x sr ws = ok rmap2 ->
    is_align (sub_region_addr sr) ws /\
    set_sub_region rmap x sr (Some 0) (size_slot x) = ok rmap2.
Proof.
  by rewrite /set_word; t_xrbindP=> hvalid hwf _ /(check_alignP hvalid hwf).
Qed.

(* TODO: better name? *)
Lemma wfr_WF_set rmap x sr rmap2 :
  wfr_WF rmap ->
  wf_sub_region sr x.(vtype) ->
  rmap2.(var_region) = Mvar.set rmap.(var_region) x sr ->
  wfr_WF rmap2.
Proof.
  move=> hwsrf hwfsr hrmap2 y sry.
  rewrite hrmap2 Mvar.setP.
  by case: eqP; [congruence|auto].
Qed.

(* We show that, under the right hypotheses, [set_sub_region] preserves
   the [valid_state] invariant.
   This lemma is used both for words and arrays.
*)
Lemma valid_state_set_sub_region rmap m0 s1 s2 sr x pk ofs ty mem2 v (rmap2 : region_map) :
  valid_state rmap m0 s1 s2 ->
  wf_sub_region sr x.(vtype) ->
  get_local pmap x = Some pk ->
  valid_pk rmap.(region_var) s2 sr pk ->
  (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + size_of ty <= size_of x.(vtype)) ->
  (forall p ws, valid_pointer mem2 p ws = valid_pointer (emem s2) p ws) ->
 (forall p ws,
    disjoint_zrange (sub_region_addr (sub_region_at_ofs sr ofs (size_of ty)))
                    (size_of (stype_at_ofs ofs ty x.(vtype)))
                    p (wsize_size ws) ->
    read_mem mem2 p ws = read_mem (emem s2) p ws) ->
  set_sub_region rmap x sr ofs (size_of ty) = ok rmap2 ->
  eq_sub_region_val x.(vtype) mem2 sr (get_var_bytes rmap2 sr.(sr_region) x) v ->
  valid_state rmap2 m0 (with_vm s1 (evm s1).[x <- pof_val x.(vtype) v]) (with_mem s2 mem2).
Proof.
  move=> hvs hwf hlx hpk hofs hvalideq hreadeq hset heqval.
  have hwf' := sub_region_at_ofs_wf hwf hofs.
  case:(hvs) => hvalid hdisj hincl hunch hrip hrsp heqvm hwfr heqmem.
  constructor => //=.
  + by move=> ??; rewrite hvalideq; apply hvalid.
  + by move=> ??; rewrite hvalideq; apply hincl.
  + case /set_sub_regionP : hset => hwritable _.
    by apply (mem_unchanged_write_slot hwf' hwritable hreadeq hunch).
  + move=> y hget; rewrite get_var_neq; first by apply heqvm.
    by rewrite /get_local in hlx; congruence.
  + case: (hwfr) => hwfsr hval hptr; split.
    + apply (wfr_WF_set hwfsr hwf).
      by have [_ ->] := set_sub_regionP hset.
    + by apply (wfr_VAL_set_sub_region hwfr hwf hofs hreadeq hset heqval).
    by apply (wfr_PTR_set_sub_region hlx hwf hpk hreadeq hofs hset hptr).
  by apply (eq_mem_source_write_slot hvs hwf' hreadeq).
Qed.

Lemma disjoint_range_valid_not_valid_U8 m p1 ws1 p2 :
  valid_pointer m p1 ws1 ->
  ~ valid_pointer m p2 U8 ->
  disjoint_range p1 ws1 p2 U8.
Proof.
  move=> /Memory.valid_pointerP [hal1 hval1] hnval.
  split.
  + by apply is_align_no_overflow.
  + by apply is_align_no_overflow; apply is_align8.
  rewrite wsize8.
  case: (Z_le_gt_dec (wunsigned p1 + wsize_size ws1) (wunsigned p2)); first by left.
  case: (Z_le_gt_dec (wunsigned p2 + 1) (wunsigned p1)); first by right.
  move=> hgt1 hgt2.
  case: hnval.
  apply /Memory.valid_pointerP; split.
  + by apply is_align8.
  move=> k; rewrite wsize8 => hk; have ->: k = 0 by lia.
  rewrite wrepr0 GRing.addr0.
  have ->: p2 = (p1 + wrepr _ (wunsigned p2 - wunsigned p1))%R.
  + by rewrite wrepr_sub !wrepr_unsigned; ssrring.ssring. (* proof from memory_model *)
  by apply hval1; lia.
Qed.

Lemma set_arr_wordP rmap m0 s1 s2 x ofs ws rmap2 :
  valid_state rmap m0 s1 s2 ->
  set_arr_word rmap x ofs ws = ok rmap2 ->
  exists sr, [/\
    Mvar.get rmap.(var_region) x = Some sr,
    is_align (sub_region_addr sr) ws &
    set_sub_region rmap x sr ofs (wsize_size ws) = ok rmap2].
Proof.
  move=> hvs.
  rewrite /set_arr_word; t_xrbindP=> sr /get_sub_regionP hget.
  have /wfr_wf hwf := hget.
  move=> _ /(check_alignP _ hwf) halign.
  by exists sr; split.
Qed.

Lemma zbetween_zone_zbetween sr1 sr2 ty1 ty2 :
  wf_sub_region sr1 ty1 ->
  wf_sub_region sr2 ty2 ->
  sr_region sr1 = sr_region sr2 ->
  zbetween_zone (sub_zone_at_ofs (sr_zone sr1) (Some 0) (size_of ty1))
                (sub_zone_at_ofs (sr_zone sr2) (Some 0) (size_of ty2)) ->
  zbetween (sub_region_addr sr1) (size_of ty1) (sub_region_addr sr2) (size_of ty2).
Proof.
  move=> hwf1 hwf2 heq.
  rewrite /zbetween_zone /zbetween !zify /=.
  rewrite (wunsigned_sub_region_addr hwf1).
  rewrite (wunsigned_sub_region_addr hwf2).
  rewrite heq.
  by lia.
Qed.

Lemma zbetween_sub_region_at_ofs sr ty ofs ws :
  wf_sub_region sr ty ->
  (∀ zofs : Z, ofs = Some zofs → 0 <= zofs ∧ zofs + wsize_size ws <= size_of ty) ->
  zbetween (sub_region_addr sr) (size_of ty)
           (sub_region_addr (sub_region_at_ofs sr ofs (wsize_size ws))) (size_of (stype_at_ofs ofs (sword ws) ty)).
Proof.
  move=> hwf hofs.
  change (wsize_size ws) with (size_of (sword ws)) in hofs.
  have hwf' := sub_region_at_ofs_wf hwf hofs.
  rewrite /zbetween !zify.
  rewrite (wunsigned_sub_region_addr hwf).
  rewrite (wunsigned_sub_region_addr hwf').
  case: ofs hofs {hwf'} => [ofs|] /=.
  + by move=> /(_ _ refl_equal); lia.
  by lia.
Qed.

Lemma zbetween_sub_region_at_ofs_option sr ofs ws i ty :
  wf_sub_region sr ty ->
  0 <= i /\ i + wsize_size ws <= size_of ty ->
  (ofs <> None -> ofs = Some i) ->
  zbetween (sub_region_addr (sub_region_at_ofs sr ofs (wsize_size ws))) (size_of (stype_at_ofs ofs (sword ws) ty))
           (sub_region_addr sr + wrepr _ i) (wsize_size ws).
Proof.
  move=> hwf hi.
  rewrite (sub_region_addr_offset (wsize_size ws)).
  case: ofs => [ofs|] /=.
  + by move=> /(_ ltac:(discriminate)) [->]; apply zbetween_refl.
  move=> _; rewrite sub_region_at_ofs_None.
  apply: (zbetween_sub_region_at_ofs hwf).
  by move=> _ [<-].
Qed.

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
  case: r1 ha => //=.
  (* Lnone *)
  + move=> vi ty1 [<-] /= s1' /write_noneP [->] h; exists s2; split => //.
    by rewrite /write_none; case: h => [ [? ->]| [-> ->]].

  (* Lvar *)
  + move=> x.
    case hlx: get_local => [pk | ]; last first.
    + t_xrbindP=> _ /check_diffP hnnew <- s1'.
      rewrite /write_var; t_xrbindP => vm1 hvm1 <- /=.
      by apply: set_varP hvm1=> [v' hv <- | hb hv <-]; rewrite /write_var /set_var hv /= ?hb /=;
        eexists;(split;first by reflexivity); apply valid_state_set_var.
    case heq: is_word_type => [ws | //]; move /is_word_typeP : heq => hty.
    case: eqP => htyv //; rewrite /write_var.
    t_xrbindP => -[xi ei] ha sr hsr rmap2 hsetw <- /= s1' vm1' hvm1' ?; subst s1' => /=.
    have he1 : sem_pexpr [::] s2 0 >>= to_int = ok 0 by done.
    have hpk := sub_region_pk_valid rmap s2 hsr.
    have [wx [wi [-> -> /= <-]]]:= check_mk_addr_ptr hvs he1 (wf_locals hlx) hpk ha.
    move: hvm1'; apply set_varP; last by rewrite {1}hty.
    move=> {ha}; case: x hty hlx hsetw => -[xty xn] xii /= ->.
    set x := {| vtype := sword ws; vname := xn |} => hlx hsetw /= w hto.
    have /(type_of_val_to_pword htyv) [w' [? ?]] := hto; subst v.
    move=> <- /=; rewrite truncate_word_u /= wrepr0 GRing.addr0.
    have hwf := sub_region_pk_wf hlx refl_equal hsr.
    have hvp: valid_pointer (emem s2) (sub_region_addr sr) ws.
    + have [halign _] := set_wordP hvs hwf hsetw.
      apply /Memory.valid_pointerP; split=> //.
      move=> k hk.
      apply: (valid_pointer_sub_region_at_ofs hvs hwf).
      + by rewrite wsize8 /=; lia.
      apply is_align8.
    have /Memory.writeV -/(_ w') [mem2 hmem2] := hvp.
    rewrite hmem2 /=; eexists;split;first by reflexivity.
    (* valid_state update word *)
    have [_ hset] := set_wordP hvs hwf hsetw.
    rewrite -hto.
    apply: (valid_state_set_sub_region hvs hwf hlx hpk _ _ _ hset (v:=Vword w')).
    + by move=> _ [<-]; lia.
    + by move=> ??; apply (Memory.write_valid _ _ hmem2).
    + move=> p ws' hdisj.
      apply (Memory.writeP_neq hmem2).
      apply: disjoint_zrange_incl_l hdisj.
      (* TODO: why cannot we reason by inclusion of sub_regions as usual ?
         We have to unfold and it works because it is (Some 0) *)
      by rewrite /sub_region_at_ofs /= Z.add_0_r; apply zbetween_refl.
    split; last by rewrite htyv.
    move=> off hmem w0 hget.
    rewrite (Memory.write_read8 _ hmem2).
    have hoff := get_val_byte_bound hget.
    have hoff': forall zofs, Some off = Some zofs → 0 <= zofs ∧ zofs + size_of sword8 <= size_slot x.
    + by move=> _ [<-]; move: hoff; rewrite /= wsize8; lia.
    have hwf' := sub_region_at_ofs_wf hwf hoff'.
    rewrite {1}(sub_region_addr_offset (wsize_size U8)).
    rewrite (wunsigned_sub_region_addr hwf).
    rewrite (wunsigned_sub_region_addr hwf').
    rewrite /= Z.add_assoc Z.add_simpl_l.
    move: hget; rewrite /get_val_byte /get_val /array_of_val; t_xrbindP=> a a' ha ?; subst a'.
    rewrite (WArray.set_get8 _ ha) Z.sub_0_r.
    by move: (hoff); rewrite -!zify htyv; move=> /= ->.

  (* Lmem *)
  + move=> ws x e1; t_xrbindP => _ /check_varP hx _ /check_diffP hnnew e1' /(alloc_eP hvs) he1 <-.
    move=> s1' xp ? hgx hxp w1 v1 /he1 he1' hv1 w hvw mem2 hw <- /=.
    have := get_var_kindP hvs hx hnnew; rewrite /get_gvar /= => /(_ _ hgx) -> /=.
    rewrite he1' hxp /= hv1 /= hvw /=.
    have hvp1 := write_mem_valid_pointer hw.
    have hvp2: valid_pointer (emem s2) (xp + w1) ws.
    + by apply /Memory.readV; assert (h := vs_eq_mem hvp1); rewrite -h; apply /Memory.readV.
    have /Memory.writeV -/(_ w) [mem2' hmem2] := hvp2.
    rewrite hmem2 /=; eexists;split;first reflexivity.
    (* valid_state update mem *)
    case:(hvs) => hvalid hdisj hincl hunch hrip hrsp heqvm hwfr heqmem.
    constructor => //=.
    + by move=> ??; rewrite (Memory.write_valid _ _ hmem2); apply hvalid.
    + by move=> ???; rewrite (Memory.write_valid _ _ hw); apply hdisj.
    + by move=> ??; rewrite (Memory.write_valid _ _ hw) (Memory.write_valid _ _ hmem2); apply hincl.
    + move=> p hvalid2; rewrite (Memory.write_valid _ _ hw) => hvalid3 hdisj2.
      rewrite (hunch p hvalid2 hvalid3 hdisj2).
      symmetry; apply (Memory.writeP_neq hmem2).
      by apply (disjoint_range_valid_not_valid_U8 hvp1 hvalid3).
    + case: (hwfr) => hwfsr hval hptr; split=> //.
      + move=> y sry bytes vy hgvalid hgy.
        assert (hwfy := check_gvalid_wf hwfsr hgvalid).
        have hreadeq := Memory.writeP_neq hmem2.
        apply: (eq_sub_region_val_disjoint_zrange hreadeq _ (hval _ _ _ _ hgvalid hgy)).
        apply disjoint_zrange_sym.
        apply (disjoint_zrange_incl_l (zbetween_sub_region_addr hwfy)).
        by apply (hdisj _ _ _ hwfy.(wfr_slot)).
      move=> y sry hgy.
      have [pk [hgpk hvpk]] := hptr _ _ hgy; exists pk; split => //.
      case: pk hgpk hvpk => //= s ofs ws' z f hgpk hread /hread <-.
      apply: (Memory.writeP_neq hmem2).
      assert (hwf' := sub_region_stkptr_wf (wf_locals hgpk)).
      apply disjoint_zrange_sym.
      apply: (disjoint_zrange_incl_l (zbetween_sub_region_addr hwf')).
      by apply (hdisj _ _ _ hwf'.(wfr_slot)).
    + move=> p ws'; rewrite (Memory.write_valid _ _ hw) => hv.
      by apply: Memory.read_write_any_mem hw hmem2 => //; apply heqmem.

  (* Laset *)
  move=> aa ws x e1; t_xrbindP => e1' /(alloc_eP hvs) he1.
  move=> hr2 s1'; apply on_arr_varP => n t hty hxt.
  t_xrbindP => i1 v1 /he1 he1' hi1 w hvw t' htt' vm1 hvm1 ?; subst s1'.
  case hlx: get_local hr2 => [pk | ]; last first.
  + t_xrbindP=> _ /check_diffP hnnew <-.
    have /get_var_kindP -/(_ _ hnnew hxt) : get_var_kind pmap (mk_lvar x) = ok None.
    + by rewrite /get_var_kind /= hlx.
    rewrite /get_gvar /= => hxt2.
    rewrite he1' /= hi1 hxt2 /= hvw /= htt' /=.
    apply: set_varP hvm1=> [v' hv <- | ]; last by rewrite {1} hty.
    rewrite /set_var hv /=.
    by eexists;(split;first by reflexivity); apply valid_state_set_var.
  t_xrbindP => rmap2 /set_arr_wordP [sr [hget hal hset]] [xi ei] ha <- /=.
  have {he1} he1 : sem_pexpr [::] s2 e1' >>= to_int = ok i1 by rewrite he1'.
  have /wfr_ptr [pk' [hlx' hpk]] := hget.
  have hgvalid := check_gvalid_lvar hget.
  move: hlx'; rewrite hlx => -[?]; subst pk'.
  have [wx [wi [-> -> /= <-]]]:= check_mk_addr_ptr hvs he1 (wf_locals hlx) hpk ha.
  move: hvm1; apply set_varP; last by rewrite {1}hty.
  move=> {ha}; case: x hty hlx hxt hget hset hgvalid => -[xty xn] xii /= ->.
  set x := {| vtype := sarr n; vname := xn |} => hlx hxt hget hset hgvalid /= ti [?] ?; subst ti vm1.
  rewrite hvw /=.
  have /wfr_wf hwf := hget.
  have [hge0 hlen haa] := WArray.set_bound htt'.
  have hvp: valid_pointer (emem s2) (sub_region_addr sr + wrepr _ (i1 * mk_scale aa ws)) ws.
  + apply (valid_pointer_sub_region_at_ofs _ hwf (conj hge0 hlen)).
    apply is_align_add => //.
    by apply arr_is_align.
  have /Memory.writeV -/(_ w) [mem2 hmem2] := hvp.
  rewrite hmem2 /=; eexists;split;first by reflexivity.
  (* valid_state update array *)
  have hofs: forall zofs, mk_ofsi aa ws e1' = Some zofs ->
    0 <= zofs /\ zofs + size_of (sword ws) <= size_slot x.
  + move=> zofs heq.
    have := mk_ofsiP he1 (aa:=aa) (sz:=ws).
    by rewrite heq; move=> /(_ ltac:(discriminate)) [->] /=; lia.
  have hvalideq := Memory.write_valid _ _ hmem2.
  apply: (valid_state_set_sub_region hvs hwf hlx hpk hofs hvalideq _ hset (v:=Varr t')).
  + move=> p ws' hdisj.
    apply (Memory.writeP_neq hmem2).
    apply: disjoint_zrange_incl_l hdisj.
    by apply: (zbetween_sub_region_at_ofs_option hwf _ (mk_ofsiP he1)).
  split=> //.
  move=> off hmem w0 hget'.
  rewrite (Memory.write_read8 _ hmem2) /=.
  rewrite (sub_region_addr_offset (wsize_size U8)) (sub_region_addr_offset (wsize_size ws)).
  have hwf' : wf_sub_region (sub_region_at_ofs sr (Some off) (wsize_size U8)) sword8.
  + change (wsize_size U8) with (size_of sword8).
    apply: (sub_region_at_ofs_wf hwf).
    move=> _ [<-] /=; rewrite wsize8.
    by have /= := get_val_byte_bound hget'; lia.
  rewrite (wunsigned_sub_region_addr hwf') {hwf'}.
  have hwf'' : wf_sub_region (sub_region_at_ofs sr (Some (i1 * mk_scale aa ws)) (wsize_size ws)) (sword ws).
  + change (wsize_size ws) with (size_of (sword ws)).
    apply: (sub_region_at_ofs_wf hwf).
    by move=> _ [<-].
  rewrite (wunsigned_sub_region_addr hwf'') {hwf''}.
  rewrite /= !Z.add_assoc Z.add_add_simpl_l_l.
  case: ifP => hle.
  + move: hget'; rewrite /get_val_byte /get_val /=.
    by rewrite (WArray.set_get8 _ htt') /= hle.
  assert (hval := wfr_val hgvalid hxt).
  case: hval => hread _.
  rewrite -sub_region_addr_offset.
  apply hread; last first.
  + rewrite -hget' /get_val_byte /get_val /=.
    by rewrite (WArray.set_get8 _ htt') /= hle.
  move: hset hmem => /set_sub_regionP [_ ->] /=.
  rewrite get_var_bytes_set_pure_bytes !eq_refl /=.
  case heq: mk_ofsi => [ofs'|//].
  have := mk_ofsiP he1 (aa:=aa) (sz:=ws).
  rewrite heq; move=> /(_ ltac:(discriminate)) [->].
  rewrite ByteSet.addE => /orP [|//].
  by move /andP : hle; rewrite /I.memi /= !zify; lia.
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
Variable (local_alloc : funname -> stk_alloc_oracle_t).

Let Pi_r s1 (i1:instr_r) s2 :=
  forall rmap1 rmap2 ii1 ii2 i2, alloc_i pmap local_alloc rmap1 (MkI ii1 i1) = ok (rmap2, MkI ii2 i2) ->
  forall s1', valid_state rmap1 m0 s1 s1' ->
  exists s2', sem_i (sCP:= sCP_stack) P' rip s1' i2 s2' /\ valid_state rmap2 m0 s2 s2'.

Let Pi s1 (i1:instr) s2 :=
  forall rmap1 rmap2 i2, alloc_i pmap local_alloc rmap1 i1 = ok (rmap2, i2) ->
  forall s1', valid_state rmap1 m0 s1 s1' ->
  exists s2', sem_I (sCP:= sCP_stack) P' rip s1' i2 s2' /\ valid_state rmap2 m0 s2 s2'.

Let Pc s1 (c1:cmd) s2 :=
  forall rmap1 rmap2 c2, fmapM (alloc_i pmap local_alloc) rmap1 c1 = ok (rmap2, c2) ->
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
(*
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
*)
Definition lea_ptr' y ptr ofs := 
  add (Pvar (mk_lvar (with_var y ptr))) (cast_const ofs).
(*
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
*)
(*
get_ofs_sub aa ws e ofs :
  get_ofs_sub aa ws e = ok ofs ->
  mk_ofsiP *)

Local Opaque arr_size.

(* TODO: move to WArray *)
Lemma get_sub_bound lena aa ws len (a:WArray.array lena) p a2 :
  WArray.get_sub aa ws len a p = ok a2 ->
  0 <= p * mk_scale aa ws /\ p * mk_scale aa ws + arr_size ws len <= lena.
Proof. by rewrite /WArray.get_sub; case: ifP => //; rewrite !zify. Qed.

Lemma get_ofs_subP gd s i aa ws e ofs :
  sem_pexpr gd s e >>= to_int = ok i ->
  get_ofs_sub aa ws e = ok ofs ->
  ofs = i * mk_scale aa ws.
Proof.
  move=> he; rewrite /get_ofs_sub.
  case heq: mk_ofsi => [ofs'|//] [<-].
  have := mk_ofsiP he (aa:=aa) (sz:=ws).
  by rewrite heq; move=> /(_ ltac:(discriminate)) [->].
Qed.

Lemma get_var_bytes_set_move rmap x sr r y :
  get_var_bytes (set_move rmap x sr) r y =
    let bytes := get_var_bytes rmap r y in
    if sr_region sr != r then
      bytes
    else
      if x == y then
        ByteSet.full (interval_of_zone sr.(sr_zone))
      else
        bytes.
Proof.
  rewrite /get_var_bytes /=.
  rewrite get_bytes_map_setP.
  case: eqP => //= ->.
  by apply get_bytes_setP.
Qed.

Lemma check_gvalid_set_move rmap x sr y sry bytes :
  check_gvalid (set_move rmap x sr) y = Some (sry, bytes) ->
    [/\ ~ is_glob y, x = gv y, sr = sry &
        bytes = ByteSet.full (interval_of_zone sr.(sr_zone))]
  \/
    [/\ ~ is_glob y -> x <> gv y &
        check_gvalid rmap y = Some (sry, bytes)].
Proof.
  rewrite /check_gvalid.
  case: (@idP (is_glob y)) => hg.
  + case heq: Mvar.get => [[ofs ws]|//] [<- <-].
    by right; split.
  rewrite Mvar.setP; case: eqP.
  + move=> -> [<- <-]; left; split=> //.
    by rewrite get_var_bytes_set_move !eq_refl.
  move=> hneq.
  case heq': Mvar.get => [sr'|//] [? <-]; subst sr'.
  right; split => //.
  rewrite get_var_bytes_set_move.
  case: eqP => [_|//].
  by move: hneq=> /eqP /negPf ->.
Qed.

Lemma set_arr_sub_rmap rmap x ofs len sr_from rmap2 :
  set_arr_sub rmap x ofs len sr_from = ok rmap2 ->
  rmap2.(var_region) = rmap.(var_region).
Proof.
  rewrite /set_arr_sub.
  by t_xrbindP=> _ _ _ _ <- /=.
Qed.

Lemma set_arr_subP rmap x ofs len sr_from rmap2 :
  set_arr_sub rmap x ofs len sr_from = ok rmap2 ->
  exists sr,
    Mvar.get rmap.(var_region) x = Some sr /\
    sub_region_at_ofs sr (Some ofs) len = sr_from.
Proof.
  rewrite /set_arr_sub.
  t_xrbindP=> sr /get_sub_regionP -> _ /assertP /eqP heqsub _.
  by exists sr.
Qed.

Lemma get_var_bytes_set_arr_sub rmap x srx ofs len sr rmap2 r y :
  Mvar.get rmap.(var_region) x = Some srx ->
  set_arr_sub rmap x ofs len sr = ok rmap2 ->
  get_var_bytes rmap2 r y =
    let bytes := get_var_bytes rmap r y in
    if sr_region srx != r then
      bytes
    else
      if x == y then
        ByteSet.add (interval_of_zone (sub_zone_at_ofs (sr_zone srx) (Some ofs) len)) bytes
      else bytes.
Proof.
  move=> hgetx.
  rewrite /set_arr_sub.
  t_xrbindP=> srx' /get_sub_regionP; rewrite hgetx; move=> [?]; subst srx'.
  move=> _ _ <-.
  rewrite /get_var_bytes get_bytes_map_setP.
  case: eqP => //= <-.
  rewrite get_bytes_setP.
  by case: eqP => //= <-.
Qed.

Lemma check_gvalid_set_arr_sub rmap x srx ofs len sr rmap2 y sry bytes :
  Mvar.get rmap.(var_region) x = Some srx ->
  set_arr_sub rmap x ofs len sr = ok rmap2 ->
  check_gvalid rmap2 y = Some (sry, bytes) ->
    ([/\ ~ is_glob y, x = gv y, srx = sry &
         bytes = get_var_bytes rmap2 srx.(sr_region) x]
  \/
    [/\ ~ is_glob y -> x <> gv y &
        check_gvalid rmap y = Some (sry, bytes)]).
Proof.
  move=> hgetx harr.
  rewrite /check_gvalid /=.
  rewrite (set_arr_sub_rmap harr).
  case: (@idP (is_glob y)) => hg.
  + case heq: Mvar.get => [[ofs' ws]|//] [<- <-].
    by right; split.
  case heq: Mvar.get => [sr'|//] [? <-]; subst sr'.
  case: (x =P y.(gv)).
  + move=> ?; subst x.
    by move: heq; rewrite hgetx; move=> [<-]; left.
  move=> hneq.
  right; split=> //.
  rewrite (get_var_bytes_set_arr_sub _ _ hgetx harr).
  case: eqP => //= _.
  by move: hneq=> /eqP /negPf ->.
Qed.

(* [arr_size] is sometimes automatically unfolded. We chose to unfold it
   everywhere, so that [lia] recognizes the identical terms.
   -> we made [arr_size] Opaque.
   TODO: move to WArray
*)
Lemma get_sub_get8 aa ws lena (a : WArray.array lena) len p a' aa' :
  WArray.get_sub aa ws len a p = ok a' ->
  forall ofs, 0 <= ofs < arr_size ws len ->
  WArray.get aa' U8 a' ofs = WArray.get aa' U8 a (p * mk_scale aa ws + ofs).
Proof.
  move=> hgsub ofs hofs.
  have hbound := get_sub_bound hgsub.
  rewrite /WArray.get /CoreMem.read !CoreMem.uread8_get /=.
  rewrite WArray.mk_scale_U8 !Z.mul_1_r.
  apply bind_eq.
  + rewrite /WArray.validr.
    apply bind_eq.
    + rewrite /WArray.validw !WArray.is_align8 /WArray.in_range wsize8 Z2Pos.id //=.
      case: andP; last by rewrite !zify; lia.
      by case: andP; last by rewrite !zify; lia.
    move=> ?; f_equal => /=.
    rewrite !Z.add_0_r (WArray.get_sub_zget8 _ hgsub) /=.
    by case: ifPn; last by rewrite !zify; lia.
  move=> ?.
  rewrite /WArray.uget /= (WArray.get_sub_zget8 _ hgsub) /=.
  by case: ifPn; last by rewrite !zify; lia.
Qed.

(* For the general case, we have [type_of_get_gvar]. But it is imprecise due to
   the [word] case. We have a more precise result for arrays.
*)
Lemma type_of_get_gvar_array gd vm x n (a : WArray.array n) :
  get_gvar gd vm x = ok (Varr a) ->
  x.(gv).(vtype) = sarr n.
Proof.
  rewrite /get_gvar.
  case: (is_lvar x).
  + rewrite /get_var.
    apply on_vuP => //.
    case: x => -[[ty xn] xi] xs /=.
    by case: ty => //= len t _ [hty _]; f_equal.
  by move=> /type_of_get_global.
Qed.

Lemma get_Pvar_sub_bound s1 v e y suby ofs len :
  sem_pexpr gd s1 e = ok v ->
  get_Pvar_sub e = ok (y, suby) ->
  match suby with
  | Some p => p
  | None => (0, size_slot y.(gv))
  end = (ofs, len) ->
  0 < len /\
  0 <= ofs /\ ofs + len <= size_slot y.(gv).
Proof.
  case: e => //=.
  + move=> _ _ [_ <-] [<- <-].
    split; first by apply size_of_gt0.
    by lia.
  move=> aa ws len' x e'.
  apply: on_arr_gvarP.
  t_xrbindP=> n _ hty _ i v' he' hv' _ /get_sub_bound hbound _ ofs' hofs' <- <- [<- <-].
  split=> //.
  rewrite hty.
  have {he' hv'} he' : sem_pexpr gd s1 e' >>= to_int = ok i by rewrite he'.
  by move: hofs' => /(get_ofs_subP he') ->.
Qed.

Lemma get_Pvar_subP s1 n (a : WArray.array n) e y ofsy ofs len :
  sem_pexpr gd s1 e = ok (Varr a) ->
  get_Pvar_sub e = ok (y, ofsy) ->
  match ofsy with
  | None => (0%Z, size_slot y.(gv))
  | Some p => p
  end = (ofs, len) ->
  n = Z.to_pos len /\
  exists (t : WArray.array (Z.to_pos (size_slot y.(gv)))),
    get_gvar gd (evm s1) y = ok (Varr t) /\
    forall i, 0 <= i < len ->
      WArray.get AAscale U8 a i = WArray.get AAscale U8 t (ofs + i).
Proof.
  case: e => //=.
  + move=> y' hget [? <-] [<- ?]; subst y' len.
    have -> := type_of_get_gvar_array hget.
    split=> //.
    by exists a; split.
  move=> aa ws len' x e.
  apply: on_arr_gvarP.
  move=> n1 a1 hty hget.
  (* We manually apply [rbindP], because [t_xrbindP] is a bit too aggressive. *)
  apply: rbindP => i he.
  apply: rbindP => a2 hgsub heq.
  have := Varr_inj (ok_inj heq) => {heq} -[?]; subst n => /= ?; subst a2.
  t_xrbindP=> _ /(get_ofs_subP he) -> <- <- [<- <-].
  split=> //.
  rewrite hty.
  exists a1; split=> //.
  by apply (get_sub_get8 _ hgsub).
Qed.

Lemma is_stack_ptrP vpk s ofs ws z f :
  is_stack_ptr vpk = Some (s, ofs, ws, z, f) ->
  vpk = VKptr (Pstkptr s ofs ws z f).
Proof.
  case: vpk => [|[]] => //=.
  by move=> _ _ _ _ _ [-> -> -> -> ->].
Qed.

(* is mk_addr_pexpr a good name ?
   could be pexpr_addr_from_vpk ?
*)
Lemma mk_addr_pexprP rmap s1 s2 (x : var_i) vpk sr e1 ofs :
  valid_state rmap m0 s1 s2 ->
  wf_vpk x vpk ->
  valid_vpk rmap s2 x sr vpk ->
  mk_addr_pexpr pmap rmap x vpk = ok (e1, ofs) ->
  exists w,
    sem_pexpr [::] s2 e1 >>= to_pointer = ok w /\
    sub_region_addr sr = (w + wrepr _ ofs)%R.
Proof.
  move=> hvs hwfpk hpk.
  rewrite /mk_addr_pexpr.
  case heq: is_stack_ptr => [[[[[s ws] ofs'] z] f]|]; last first.
  + by t_xrbindP=> -[x' ofs'] /(addr_from_vpkP hvs hwfpk hpk) haddr <- <-.
  move /is_stack_ptrP in heq; subst vpk.
  rewrite /= in hpk hwfpk.
  t_xrbindP=> _ /assertP /hpk hread <- <- /=.
  rewrite {1}/sub_region_addr /= (wfs_offset hwfpk) in hread.
  rewrite vs_rsp /= !zero_extend_u wrepr_add GRing.addrA hread /= truncate_word_u.
  eexists; split; first by reflexivity.
  by rewrite wrepr0 GRing.addr0.
Qed.

Lemma truncate_val_array n v v' :
  truncate_val (sarr n) v = ok v' ->
  exists m (a : WArray.array m),
    [/\ n <= m, v = Varr a & v' = Varr (WArray.inject n a)].
Proof.
  rewrite /truncate_val /=.
  t_xrbindP=> _ /to_arrI [m [a [-> hm ->]]] <-.
  exists m, a; split=> //.
  rewrite /WArray.inject.
  by case: ZltP; first by lia.
Qed.

Lemma inject_get_bound (len len' : positive) (a : WArray.array len) aa ofs w :
  WArray.get aa U8 (WArray.inject len' a) ofs = ok w ->
  ofs < len.
Proof.
  move=> /dup[] /WArray.get_bound.
  rewrite WArray.mk_scale_U8 Z.mul_1_r wsize8 => -[h1 h2 _].
  rewrite /WArray.get /CoreMem.read !CoreMem.uread8_get WArray.mk_scale_U8 Z.mul_1_r.
  rewrite /= /WArray.validr /=.
  t_xrbindP=> _ _ _ /assertP hvalidr _.
  move: hvalidr; rewrite Z.add_0_r WArray.zget_inject; last by lia.
  by case: ZltP.
Qed.

Lemma set_sub_bound aa ws lena (a : WArray.array lena) len p (b : WArray.array (Z.to_pos (arr_size ws len))) a' :
  WArray.set_sub aa a p b = ok a' ->
  0 <= p * mk_scale aa ws /\ p * mk_scale aa ws + arr_size ws len <= Z.pos lena.
Proof. by rewrite /WArray.set_sub; case: ifP => //; rewrite !zify. Qed.

Lemma set_sub_get8 aa ws lena (a : WArray.array lena) len p (b : WArray.array (Z.to_pos (arr_size ws len))) a' aa' :
  WArray.set_sub aa a p b = ok a' ->
  forall ofs,
  WArray.get aa' U8 a' ofs =
    let i := ofs - p * mk_scale aa ws in
    if (0 <=? i) && (i <? arr_size ws len) then
      WArray.get aa' U8 b i
    else WArray.get aa' U8 a ofs.
Proof.
  move=> hssub ofs.
  have hbound := set_sub_bound hssub.
  rewrite /WArray.get /CoreMem.read !CoreMem.uread8_get /=.
  rewrite WArray.mk_scale_U8 !Z.mul_1_r.
  case: ifPn.
  + rewrite !zify => hbound2.
    apply bind_eq.
    + rewrite /WArray.validr.
      apply bind_eq.
      + rewrite /WArray.validw !WArray.is_align8 /WArray.in_range wsize8 Z2Pos.id //=.
        case: andP; last by rewrite !zify; lia.
        by case: andP; last by rewrite !zify; lia.
      move=> ?; f_equal => /=.
      rewrite !Z.add_0_r (WArray.set_sub_zget8 _ hssub) /=.
      by case: ifPn; last by rewrite !zify; lia.
    move=> ?.
    rewrite /WArray.uget /= (WArray.set_sub_zget8 _ hssub) /=.
    by case: ifPn; last by rewrite !zify; lia.
  rewrite !zify => hbound2.
  apply bind_eq.
  + rewrite /WArray.validr.
    apply bind_eq=> //.
    move=> ?; f_equal => /=.
    rewrite Z.add_0_r (WArray.set_sub_zget8 _ hssub) /=.
    by case: ifPn; first by rewrite !zify; lia.
  move=> ?.
  rewrite /WArray.uget /= (WArray.set_sub_zget8 _ hssub) /=.
  by case: ifPn; first by rewrite !zify; lia.
Qed.

Lemma cast_bound len len' (a : WArray.array len) a' :
  WArray.cast len' a = ok a' ->
  len' <= len.
Proof. by rewrite /WArray.cast; case: ZleP. Qed.

Lemma castP len len' (a : WArray.array len) a' :
  WArray.cast len' a = ok a' ->
  a' = WArray.inject len' a.
Proof.
  rewrite /WArray.cast /WArray.inject.
  case: ZleP => // hle [<-].
  by case: ZltP; first by lia.
Qed.

Lemma inject_get8 (len len' : positive) (a : WArray.array len) aa ofs w :
  WArray.get aa U8 (WArray.inject len' a) ofs = ok w ->
  WArray.get aa U8 a ofs = ok w.
Proof.
  rewrite /WArray.get /CoreMem.read !CoreMem.uread8_get WArray.mk_scale_U8 Z.mul_1_r.
  rewrite /= /WArray.validr /WArray.validw /WArray.in_range /WArray.uget /= wsize8 Z.add_0_r !andbT.
  t_xrbindP=> _ _ _ /assertP /andP [/ZleP h1 /ZleP h2] /assertP -> /assertP.
  rewrite WArray.zget_inject; last by lia.
  case: ZltP => [h3|//] -> <-.
  by case: andP; last by rewrite !zify; lia.
Qed.

Lemma valid_pk_set_move (rmap:region_map) s2 x sr y pk sry :
  ~ Sv.In x pmap.(vnew) ->
  wf_local y pk ->
  valid_pk rmap s2 sry pk ->
  valid_pk (set_move rmap x sr) s2 sry pk.
Proof.
  move=> hnnew hlocal.
  case: pk hlocal => //=.
  move=> s ofs ws z f hlocal.
  rewrite /check_stack_ptr get_var_bytes_set_move.
  case: eqP => [_|//].
  case: eqP => //.
  by have := hlocal.(wfs_new); congruence.
Qed.

Lemma wfr_VAL_set_move rmap s1 s2 x sr v :
  eq_sub_region_val x.(vtype) (emem s2) sr (ByteSet.full (interval_of_zone sr.(sr_zone))) v ->
  wfr_VAL rmap s1 s2 ->
  wfr_VAL (set_move rmap x sr) (with_vm s1 (evm s1).[x <- pof_val x.(vtype) v]) s2.
Proof.
  move=> heqval hval y sry bytesy vy /check_gvalid_set_move [].
  + move=> [? ? <- ->]; subst x.
    rewrite get_gvar_eq //.
    case: heqval => hread hty'.
    apply on_vuP => //; rewrite -hty'.
    by move => ? hof hto; rewrite -hto (pto_val_pof_val hof) hty'.
  move=> [? hgvalid].
  rewrite get_gvar_neq => //.
  by apply hval.
Qed.

Lemma wfr_PTR_set_move (rmap : region_map) s2 x pk sr :
  get_local pmap x = Some pk ->
  valid_pk rmap s2 sr pk ->
  wfr_PTR rmap s2 ->
  wfr_PTR (set_move rmap x sr) s2.
Proof.
  move=> hlx hpk hptr y sry.
  have /wf_vnew hnnew := hlx.
  rewrite Mvar.setP; case: eqP.
  + move=> <- [<-].
    exists pk; split=> //.
    by apply (valid_pk_set_move _ hnnew (wf_locals hlx) hpk).
  move=> _ /hptr {pk hlx hpk} [pk [hly hpk]].
  exists pk; split=> //.
  by apply (valid_pk_set_move _ hnnew (wf_locals hly) hpk).
Qed.

(* There are 3 lemmas about [set_move] and [valid_state].
*)
Lemma valid_state_set_move rmap s1 s2 x sr pk v :
  valid_state rmap m0 s1 s2 ->
  wf_sub_region sr x.(vtype) ->
  get_local pmap x = Some pk ->
  valid_pk rmap.(region_var) s2 sr pk ->
  eq_sub_region_val x.(vtype) (emem s2) sr (ByteSet.full (interval_of_zone sr.(sr_zone))) v ->
  valid_state (set_move rmap x sr) m0 (with_vm s1 (evm s1).[x <- pof_val x.(vtype) v]) s2.
Proof.
  move=> hvs hwf hlx hpk heqval.
  case:(hvs) => hvalid hdisj hincl hunch hrip hrsp heqvm hwfr heqmem.
  constructor=> //=.
  + move=> y hget; rewrite get_var_neq; first by apply heqvm.
    by rewrite /get_local in hlx; congruence.
  case: (hwfr) => hwfsr hval hptr; split.
  + by apply (wfr_WF_set hwfsr hwf).
  + by apply (wfr_VAL_set_move heqval hval).
  by apply (wfr_PTR_set_move hlx hpk hptr).
Qed.

Lemma sub_region_at_ofs_0_wf sr ty :
  wf_sub_region sr ty ->
  wf_sub_region (sub_region_at_ofs sr (Some 0) (size_of ty)) ty.
Proof.
  move=> hwf.
  apply: (sub_region_at_ofs_wf hwf).
  by move=> _ [<-]; lia.
Qed.

(* Another lemma on [set_move] : we write in [evm s2].
   TODO: Fusionner les 2 lemmes sur set_move ??
   Ou supprimer celui-là qui est un peu spécifique ?
*)
Lemma valid_state_set_move_regptr rmap s1 s2 x sr v p :
  valid_state rmap m0 s1 s2 ->
  wf_sub_region sr x.(vtype) ->
  get_local pmap x = Some (Pregptr p) ->
  eq_sub_region_val x.(vtype) (emem s2) sr (ByteSet.full (interval_of_zone sr.(sr_zone))) v ->
  valid_state (set_move rmap x sr) m0 (with_vm s1 (evm s1).[x <- pof_val x.(vtype) v])
                                      (with_vm s2 (evm s2).[p <- pof_val p.(vtype) (Vword (sub_region_addr sr))]).
Proof.
  move=> hvs hwf hlx heqval.
  have /wf_locals /= hlocal := hlx.
  case:(hvs) => hvalid hdisj hincl hunch hrip hrsp heqvm hwfr heqmem.
  constructor=> //=.
  + rewrite get_var_neq //.
    by apply hlocal.(wfr_not_vrip).
  + rewrite get_var_neq //.
    by apply hlocal.(wfr_not_vrsp).
  + move=> y hget hnnew.
    rewrite get_var_neq; last by rewrite /get_local in hlx; congruence.
    rewrite get_var_neq; last by have := hlocal.(wfr_new); congruence.
    by apply heqvm.
  case: (hwfr) => hwfsr hval hptr; split.
  + by apply (wfr_WF_set hwfsr hwf).
  + move=> y sry bytesy vy.
    move=> /(check_gvalid_set_move) [].
    + move=> [? ? <- ->]; subst x.
      rewrite get_gvar_eq //.
      case: heqval => hread hty'.
      apply on_vuP => //; rewrite -hty'.
      by move => ? hof hto; rewrite -hto (pto_val_pof_val hof) hty'.
    move=> [? hgvalid].
    rewrite get_gvar_neq => //.
    by apply hval.
  move=> y sry.
  rewrite Mvar.setP; case: eqP.
  + move=> <- [<-].
    exists (Pregptr p); split=> //=.
    rewrite get_var_eq.
    by rewrite hlocal.(wfr_rtype).
  move=> hneq /hptr [pk [hly hpk]].
  exists pk; split=> //.
  case: pk hly hpk => //=.
  + move=> p2 hly.
    rewrite get_var_neq //.
    by apply (hlocal.(wfr_distinct) hly hneq).
  move=> s ofs ws z f hly.
  rewrite /check_stack_ptr get_var_bytes_set_move.
  case: eqP => [_|//].
  case: eqP => //.
  have /is_sarrP [n hty] := hlocal.(wfr_type).
  by have /wf_locals /wfs_ftype := hly; congruence.
Qed.

Lemma var_region_not_new rmap s1 s2 x sr :
  valid_state rmap m0 s1 s2 ->
  Mvar.get rmap.(var_region) x = Some sr ->
  ~ Sv.In x pmap.(vnew).
Proof. by move=> hvs /wfr_ptr [_ [/wf_vnew ? _]]. Qed.
(*
Lemma check_gvalid_set_stack_ptr rmap s1 s2 s ws z f y sry bytes :
  valid_state rmap m0 s1 s2 ->
  Sv.In f pmap.(vnew) ->
  check_gvalid (set_stack_ptr rmap s ws z f) y = Some (sry, bytes) ->
  exists bytes',
    [/\ check_gvalid rmap y = Some (sry, bytes'),
        ~ is_glob y -> f <> gv y &
        bytes =
          if (sub_region_stkptr s ws z).(sr_region) != sry.(sr_region) then bytes'
          else ByteSet.remove bytes' (interval_of_zone (sub_zone_at_ofs (sub_region_stkptr s ws z).(sr_zone) (Some 0) (wsize_size Uptr)))].
Proof.
  move=> hvs hnew.
  rewrite /check_gvalid /=.
  case: (@idP (is_glob y)) => hg.
  + case heq: Mvar.get => [[ofs ws']|//] [<- <-].
    eexists; split=> //.
    by case: eqP.
  case heq: Mvar.get => [sr|//] [<- <-].
  have hneq: f <> y.(gv).
  + by move /var_region_not_new : heq; congruence.
  eexists; split=> //.
  rewrite get_var_bytes_set_pure_bytes.
  by have /eqP /negPf -> := hneq.
Qed.
*)
Lemma check_gvalid_set_stack_ptr rmap s1 s2 s ws z f y sry bytes x sr :
  valid_state rmap m0 s1 s2 ->
  ~ Sv.In x pmap.(vnew) ->
  Sv.In f pmap.(vnew) ->
  check_gvalid (set_stack_ptr (set_move rmap x sr) s ws z f) y = Some (sry, bytes) ->
  exists bytes',
    [/\ check_gvalid (set_move rmap x sr) y = Some (sry, bytes'),
        ~ is_glob y -> f <> gv y &
        bytes =
          if (sub_region_stkptr s ws z).(sr_region) != sry.(sr_region) then bytes'
          else ByteSet.remove bytes' (interval_of_zone (sub_zone_at_ofs (sub_region_stkptr s ws z).(sr_zone) (Some 0) (wsize_size Uptr)))].
Proof.
  move=> hvs hnnew hnew.
  rewrite /check_gvalid /=.
  case: (@idP (is_glob y)) => hg.
  + case heq: Mvar.get => [[ofs ws']|//] [<- <-].
    eexists; split=> //.
    by case: eqP.
  case heq: Mvar.get => [sr'|//] [<- <-].
  have hneq: f <> y.(gv).
  + move: heq; rewrite Mvar.setP.
    case: eqP => [|_].
    + by congruence.
    by move=> /var_region_not_new; congruence.
  eexists; split=> //.
  rewrite get_var_bytes_set_pure_bytes.
  by have /eqP /negPf -> := hneq.
Qed.

Lemma valid_pk_set_stack_ptr (rmap : region_map) s2 x s ofs ws z f mem2 y pk sr:
  wf_stkptr x s ofs ws z f ->
  (forall p ws,
    disjoint_range (sub_region_addr (sub_region_at_ofs (sub_region_stkptr s ws z) (Some 0) Uptr)) Uptr p ws ->
    read_mem mem2 p ws = read_mem (emem s2) p ws) ->
  x <> y ->
  get_local pmap y = Some pk ->
  valid_pk rmap s2 sr pk ->
  valid_pk (set_stack_ptr rmap s ws z f) (with_mem s2 mem2) sr pk.
Proof.
  move=> hlocal hreadeq hneq.
  case: pk => //= s1 ofs1 ws1 z1 f1 hly hpk.
  have hwf := sub_region_at_ofs_0_wf (sub_region_stkptr_wf hlocal).
  assert (hwf1 := sub_region_stkptr_wf (wf_locals hly)).
  rewrite /check_stack_ptr get_var_bytes_set_pure_bytes.
  case: eqP => heqr /=.
  + have hneqf := hlocal.(wfs_distinct) hly hneq.
    have /eqP /negPf -> := hneqf.
    move=> /mem_remove [] /hpk <-.
    rewrite disjoint_interval_of_zone // => hdisj.
    apply hreadeq.
    apply (disjoint_zones_disjoint_zrange hwf hwf1 heqr).
    apply: disjoint_zones_incl_l hdisj.
    by apply (zbetween_zone_sub_zone_at_ofs_0 hwf).
  move=> /hpk <-.
  apply hreadeq.
  apply (disjoint_zrange_incl (zbetween_sub_region_addr hwf) (zbetween_sub_region_addr hwf1)).
  apply (disjoint_writable hwf.(wfr_slot) hwf1.(wfr_slot)); last by rewrite hwf.(wfr_writable).
  by move=> /(wf_region_slot_inj hwf hwf1).
Qed.

Lemma valid_state_set_stack_ptr rmap s1 s2 x s ofs ws z f mem2 sr v :
  valid_state rmap m0 s1 s2 ->
  wf_sub_region sr x.(vtype) ->
  get_local pmap x = Some (Pstkptr s ofs ws z f) ->
  (forall p ws,
    valid_pointer mem2 p ws = valid_pointer (emem s2) p ws) ->
  (forall p ws,
    disjoint_range (sub_region_addr (sub_region_at_ofs (sub_region_stkptr s ws z) (Some 0) U64)) Uptr p ws ->
    read_mem mem2 p ws = read_mem (emem s2) p ws) ->
  read_mem mem2 (sub_region_addr (sub_region_stkptr s ws z)) U64 = ok (sub_region_addr sr) ->
  eq_sub_region_val x.(vtype) (emem s2) sr (ByteSet.full (interval_of_zone sr.(sr_zone))) v ->
  valid_state (set_stack_ptr (set_move rmap x sr) s ws z f) m0 (with_vm s1 (evm s1).[x <- pof_val x.(vtype) v]) (with_mem s2 mem2).
Proof.
  move=> hvs hwf hlx hvalideq hreadeq hreadptr heqval.
  have /wf_locals hlocal := hlx.
  have hwfs := sub_region_stkptr_wf hlocal.
  have hwfs' := sub_region_at_ofs_0_wf hwfs.
  case:(hvs) => hvalid hdisj hincl hunch hrip hrsp heqvm hwfr heqmem.
  constructor=> //=.
  + by move=> ??; rewrite hvalideq; apply hvalid.
  + by move=> ??; rewrite hvalideq; apply hincl.
  + by apply (mem_unchanged_write_slot hwfs' refl_equal hreadeq hunch).
  + move=> y hget; rewrite get_var_neq; first by apply heqvm.
    by rewrite /get_local in hlx; congruence.
  case: (hwfr) => hwfsr hval hptr; split.
  + by apply (wfr_WF_set hwfsr hwf).
  + move=> y sry bytesy vy /(check_gvalid_set_stack_ptr hvs (wf_vnew hlx) hlocal.(wfs_new)).
    move=> {bytesy} [bytesy [hgvalidy ? ->]] hgety.
    have /(check_gvalid_wf (wfr_WF_set hwfsr hwf _)) -/(_ refl_equal) hwfy := hgvalidy.
    assert (heqvaly := wfr_VAL_set_move heqval wfr_val hgvalidy hgety).
    case: eqP => heqr /=.
    + by apply (eq_sub_region_val_same_region hwfs' hwfy heqr hreadeq heqvaly).
    by apply (eq_sub_region_val_disjoint_regions hwfs' hwfy heqr refl_equal hreadeq heqvaly).
  + move=> y sry.
    rewrite Mvar.setP.
    case: eqP.
    + move=> <- [<-].
      by exists (Pstkptr s ofs ws z f); split.
    move=> hneq /wfr_ptr [pky [hly hpky]].
    exists pky; split=> //.
    apply (valid_pk_set_stack_ptr hlocal hreadeq hneq hly).
    by apply (valid_pk_set_move sr (wf_vnew hlx) (wf_locals hly) hpky).
  by apply (eq_mem_source_write_slot hvs hwfs' hreadeq).
Qed.

Lemma valid_state_set_arr_sub rmap s1 s2 x sr pk ofs len sr_from rmap2 v :
  valid_state rmap m0 s1 s2 ->
  Mvar.get rmap.(var_region) x = Some sr ->
  get_local pmap x = Some pk ->
  set_arr_sub rmap x ofs len sr_from = ok rmap2 ->
  eq_sub_region_val x.(vtype) (emem s2) sr (get_var_bytes rmap2 sr.(sr_region) x) v ->
  valid_state rmap2 m0 (with_vm s1 (evm s1).[x <- pof_val x.(vtype) v]) s2.
Proof.
  move=> hvs hgetx hlx harr heqval.
  case:(hvs) => hvalid hdisj hincl hunch hrip hrsp heqvm hwfr heqmem.
  constructor => //=.
  + move=> y hgety; rewrite get_var_neq; first by apply heqvm.
    by rewrite /get_local in hlx; congruence.
  case: (hwfr) => hwfsr hval hptr; split.
  + rewrite /wfr_WF.
    by rewrite (set_arr_sub_rmap harr).
  + move=> y sry bytesy vy.
    move=> /(check_gvalid_set_arr_sub hgetx harr) [].
    + move=> [? ? <- ->]; subst x.
      rewrite get_gvar_eq //.
      case: heqval => hread hty.
      apply on_vuP => //; rewrite -hty.
      by move => ? hof hto; rewrite -hto (pto_val_pof_val hof) hty.
    move=> [? hgvalid].
    rewrite get_gvar_neq => //.
    by apply hval.
  move=> y sry.
  rewrite (set_arr_sub_rmap harr).
  move=> /hptr [pky [hly hpky]].
  exists pky; split=> //.
  case: pky hly hpky => //=.
  move=> s ofs' ws z f hly heq.
  rewrite /check_stack_ptr (get_var_bytes_set_arr_sub _ _ hgetx harr).
  case: eqP => // _.
  case: eqP => //.
  have /wf_vnew := hlx.
  by have /wf_locals /wfs_new := hly; congruence.
Qed.

(* TODO: find better name *)
Lemma inject_self n (a : WArray.array n) : WArray.inject n a = a.
Proof. by rewrite /WArray.inject Z.ltb_irrefl; case: a. Qed.

Lemma lea_ptrP s1 e i x ofs w s2 :
  sem_pexpr [::] s1 e >>= to_pointer = ok i ->
  write_lval [::] x (Vword (i + wrepr _ ofs)) s1 = ok s2 ->
  sem_i P' w s1 (lea_ptr x e ofs) s2.
Proof.
  move=> he hx.
  constructor.
  rewrite /sem_sopn /= P'_globs /sem_sop2 /=.
  move: he; t_xrbindP=> _ -> /= -> /=.
  by rewrite !zero_extend_u hx.
Qed.

Lemma mov_ptrP s1 e i x w s2 :
  sem_pexpr [::] s1 e >>= to_pointer = ok i ->
  write_lval [::] x (Vword i) s1 = ok s2 ->
  sem_i P' w s1 (mov_ptr x e) s2.
Proof.
  move=> he hx.
  constructor.
  rewrite /sem_sopn P'_globs /= /exec_sopn /=.
  move: he; t_xrbindP=> _ -> /= -> /=.
  by rewrite hx.
Qed.

Lemma mov_ofsP s1 e i x ofs w mk s2 :
  sem_pexpr [::] s1 e >>= to_pointer = ok i ->
  write_lval [::] x (Vword (i + wrepr _ ofs)) s1 = ok s2 ->
  sem_i P' w s1 (mov_ofs x mk e ofs) s2.
Proof.
  case: mk.
  + by apply lea_ptrP.
  rewrite /=.
  case: eqP => [->|_].
  + rewrite wrepr0 GRing.addr0.
    by apply mov_ptrP.
  by apply lea_ptrP.
Qed.

(* TODO: étrange, on peut prendre n'importe quel n ?
   Il faut juste que ce soit de la forme d'un tableau ?
   On peut pas juste avoir type_of_val v = sarr n / is_sarr (type_of_val v)
   ou quelque chose de la forme
   Let v := sem_pexpr gd s1 e in to_arr v = ok v ?
   -> sans doute pour coller à la def de [sem_i]
   TODO: prove something about truncate_val_array ?
   TODO: do we need hm and hn?
   TODO: is_nop fait un check différent des autres. Uniformiser ?
*)
Lemma alloc_array_moveP s1 s2 s1' rmap1 rmap2 r e v v' n i2 : 
  valid_state rmap1 m0 s1 s2 ->
  sem_pexpr gd s1 e = ok v ->
  truncate_val (sarr n) v = ok v' ->
  write_lval gd r v' s1 = ok s1' ->
  alloc_array_move pmap rmap1 r e = ok (rmap2, i2) → 
  ∃ s2' : estate, sem_i P' rip s2 i2 s2' ∧ valid_state rmap2 m0 s1' s2'.
Proof.
  move=> hvs he htr hw.
  have [m [a [hm hv hv']]] := truncate_val_array htr; subst v v'.
  rewrite /alloc_array_move.
  t_xrbindP=> -[x ofsx] hgetr [y ofsy] hgete.
  case hkindy: (get_var_kind pmap y) => [vk|] //.
  case hofsy: (match ofsy with
               | Some p => p
               | None => (0, size_slot (gv y))
               end) => [ofs len].
  case: vk hkindy => [vpky|//] hkindy.
  have [hlen hofs] := get_Pvar_sub_bound he hgete hofsy.
  have hofs': forall zofs, Some ofs = Some zofs -> 0 <= zofs /\ zofs + len <= size_slot y.(gv).
  + by move=> _ [<-].
  t_xrbindP=> -[[[sry' mk] ey] ofs2'] _ <-.
  t_xrbindP=> _ /(check_vpkP hofs' hkindy) [sry [bytesy [hgvalidy -> hmemy]]].
  assert (hwfy := check_gvalid_wf wfr_wf hgvalidy).
   have hwfy': wf_sub_region (sub_region_at_ofs sry (Some ofs) len) (sarr (Z.to_pos len)).
  + move: hofs'.
    have {1 2}-> : len = size_of (sarr (Z.to_pos len)) by rewrite /= Z2Pos.id.
    by apply: (sub_region_at_ofs_wf hwfy).
  have hwfpky := get_var_kind_wf hkindy.
  have hpky: valid_vpk rmap1 s2 y.(gv) sry vpky.
  + have /wfr_gptr := hgvalidy.
    by rewrite hkindy => -[_ [[]] <-].
  move=> [e1 ofs2] /(mk_addr_pexprP _ hwfpky hpky) [w [he1 haddr]] ? <- <- ?; subst sry' ofs2'.
  have [? [ay [hgety hay]]] := get_Pvar_subP he hgete hofsy; subst m.

  have heqval': forall nx off w',
    WArray.get AAscale U8 (WArray.inject nx (WArray.inject n a)) off = ok w' ->
    read_mem (emem s2) (sub_region_addr (sub_region_at_ofs sry (Some ofs) len) + wrepr U64 off) U8 = ok w'.
  + move=> nx off w'.
    rewrite -sub_region_addr_offset -GRing.addrA -wrepr_add.
    move=> /inject_get8 /inject_get8.
    move=> /dup[] /(@get_val_byte_bound (Varr a)) /=; rewrite Z2Pos.id // => hoff.
    rewrite hay //.
    assert (hval := wfr_val hgvalidy hgety).
    case: hval => hread _.
    apply hread.
    rewrite memi_mem_U8; apply: subset_mem hmemy; rewrite subset_interval_of_zone.
    rewrite -(sub_zone_at_ofs_compose _ _ _ len).
    apply zbetween_zone_byte => //.
    by apply zbetween_zone_refl.

  case: r hgetr hw => //.
  + move=> _ [-> <-].
    rewrite /write_lval /write_var; t_xrbindP=> vm1'; apply: set_varP; last first.
    + by move=> /is_sboolP h1 h2; elimtype False; move: h2; rewrite h1.
    case: x => -[xty xn] xii; case: xty => //.
    move=> nx _ [<-] <- <-.
    set x := {| vname := xn |}.
    case hlx: (get_local pmap x) => [pk|//].
    have /wf_locals hlocal := hlx.

    have heqval: forall bytes,
      eq_sub_region_val x.(vtype) (emem s2) (sub_region_at_ofs sry (Some ofs) len)
                        bytes (Varr (WArray.inject nx (WArray.inject n a))).
    + move=> bytes.
      split=> // off hmem w'.
      by apply heqval'.

    case: pk hlx hlocal.
    + t_xrbindP=> s ofs' ws z sc hlx hlocal _ /assertP /eqP heqsub <- <-.
      exists s2; split; first by constructor.
      (* valid_state update *)
      rewrite -(inject_self (WArray.inject _ _)).
      have := sub_region_direct_wf hlocal; rewrite heqsub => hwf.
      by apply: (valid_state_set_move hvs hwf hlx _ (heqval _)).
    + move=> p hlx hlocal.
      rewrite /get_addr /=.
      t_xrbindP=> _ _ /assertP hnx <- <- <-.
      set vp := pof_val p.(vtype) (Vword (sub_region_addr (sub_region_at_ofs sry (Some ofs) len))).
      exists (with_vm s2 (evm s2).[p <- vp]); split.
      + rewrite /vp -sub_region_addr_offset haddr -GRing.addrA -wrepr_add.
        apply (mov_ofsP _ _ he1).
        by case: (p) hlocal.(wfr_rtype) => ? pn /= ->.
      (* valid_state update *)
      rewrite -(inject_self (WArray.inject _ _)).
      have hwf: wf_sub_region (sub_region_at_ofs sry (Some ofs) len) x.(vtype).
      + apply: (wf_sub_region_subtype _ hwfy').
        by rewrite /= Z2Pos.id.
      apply (valid_state_set_move_regptr hvs hwf hlx (heqval _)).
    move=> s ofs' ws z f hlx hlocal.
    rewrite /get_addr /=.
    t_xrbindP=> -[_ _] {i2}i2 hi2 [<- <-] [<- <-].

    have {hi2} [hwf [mem2 [hsemi hvalideq hreadeq hreadptr]]]:
      wf_sub_region (sub_region_at_ofs sry (Some ofs) len) x.(vtype) /\
      exists mem2,
      [/\ sem_i P' rip s2 i2 (with_mem s2 mem2),
          (forall p ws, valid_pointer mem2 p ws = valid_pointer (emem s2) p ws),
          (forall p ws,
            disjoint_range (sub_region_addr (sub_region_at_ofs (sub_region_stkptr s ws z) (Some 0) U64)) U64 p ws ->
            read_mem mem2 p ws = read_mem (emem s2) p ws) &
          read_mem mem2 (sub_region_addr (sub_region_stkptr s ws z)) U64 =
            ok (sub_region_addr (sub_region_at_ofs sry (Some ofs) len))].
    + move: hi2.
      case: ifP.
      + case heq: Mvar.get => [srx|//] /andP [/eqP heqsub hcheck] [<-].
        split.
        + rewrite -heqsub.
          by apply /wfr_wf.
        exists (emem s2); split=> //.
        + by case: (s2); constructor.
        + have /wfr_ptr := heq; rewrite hlx => -[_ [[<-] hpk]].
          rewrite -heqsub.
          by apply hpk.
      t_xrbindP=> _ _ /assertP hnx <-.
      have hwf := sub_region_stkptr_wf hlocal.
      split.
      + apply: wf_sub_region_subtype hwfy'.
        by rewrite /= Z2Pos.id.
      have hal: is_align (sub_region_addr (sub_region_stkptr s ws z)) U64.
      + rewrite /sub_region_addr /=.
        apply is_align_add.
        + apply (is_align_le hvs hlocal.(wfs_align_ptr)).
          have /= <- := hwf.(wfr_align).
          by apply (slot_align hwf.(wfr_slot)).
        by apply hlocal.(wfs_offset_align).
      have hvp := valid_pointer_sub_region_addr hvs hwf hal.
      have /Memory.writeV -/(_ (w + wrepr U64 (ofs2 + ofs))%R) [mem2 hmem2] := hvp.
      exists mem2; split.
      + apply (mov_ofsP _ _ he1).
        rewrite /= vs_rsp /= !zero_extend_u.
        rewrite wrepr_add GRing.addrA.
        by rewrite -hlocal.(wfs_offset) hmem2.
      + by move=> ??; apply (Memory.write_valid _ _ hmem2).
      + move=> ??.
        (* TODO : here again, why do we have to unfold? *)
        rewrite /sub_region_at_ofs /= Z.add_0_r.
        by apply (Memory.writeP_neq hmem2).
      rewrite (Memory.writeP_eq hmem2).
      by rewrite wrepr_add GRing.addrA -haddr -sub_region_addr_offset.

    exists (with_mem s2 mem2); split=> //.
    rewrite -(inject_self (WArray.inject _ _)).
    by apply (valid_state_set_stack_ptr hvs hwf hlx hvalideq hreadeq hreadptr (heqval _)).
  (* interestingly, we can prove that n = Z.to_pos len = Z.to_pos (arr_size ws len2)
     but it does not seem useful
  *)
  move=> aa ws len2 /=.
  t_xrbindP=> _ e2 ofs3 hofs3 -> ?; subst ofsx.
  apply: on_arr_varP.
  t_xrbindP=> nx ax htyx hxa i v2 he2 hv2 _ /castP -> a2 ha vm1'.
  have {he2 hv2} he2 : sem_pexpr gd s1 e2 >>= to_int = ok i.
  + by rewrite he2.
  have {hofs3} ? := get_ofs_subP he2 hofs3; subst ofs3.
  apply: set_varP; last by rewrite {1}htyx.
  case: x htyx hxa => -[_ xn] xii /= ->.
  set x := {| vname := xn |} => hxa.
  move=> /= _ [<-] <- <-.
  case hlx: (get_local pmap x) => //.
  t_xrbindP=> rmap2' harr ? <-; subst rmap2'.
  exists s2; split; first by constructor.
  (* TODO: set_arr_sub very similar to set_move + checks !!
     Can we factorize ? not sure
     Can we make a prettier proof or do we necessarily need to go into details ?
  *)
  have [srx [hgetx heqsub]] := set_arr_subP harr.
  apply (valid_state_set_arr_sub hvs hgetx hlx harr (v := Varr a2)).
  split=> //.
  move=> off hmem w'.
  rewrite /get_val_byte get_val_array (set_sub_get8 _ ha) /=.
  case: ifPn => [_|].
  + rewrite -{2}(Zplus_minus (i * mk_scale aa ws) off).
    move: {off hmem} (off - i * mk_scale aa ws) => off.
    rewrite wrepr_add GRing.addrA (sub_region_addr_offset (arr_size ws len2)) heqsub.
    apply heqval'.
  rewrite !zify => hbound.
  have hgvalidx := check_gvalid_lvar (x:={|v_var := x; v_info := xii|}) hgetx.
  case: (wfr_val hgvalidx hxa) => hread _.
  apply hread.
  move: hmem.
  rewrite (get_var_bytes_set_arr_sub _ _ hgetx harr) !eq_refl /=.
  rewrite ByteSet.addE => /orP [|//].
  by rewrite /I.memi /= !zify; lia.
Qed.

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
