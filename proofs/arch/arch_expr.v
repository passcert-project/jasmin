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


(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Export arch_decl compiler_util.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Section.

Context `{tS : ToString}.

Definition of_string (s : string) :=
  assoc strings s.

(* -------------------------------------------------------------------- *)
Lemma to_stringK : pcancel to_string of_string.
Proof.
move=> r; rewrite /of_string stringsE; apply /(@assocP _ ceqT_eqType).
+ rewrite -map_comp (map_inj_uniq (T1:=ceqT_eqType)) //.
  + by apply: (enum_uniq (T:=cfinT_finType)).
  by apply inj_to_string.
apply: (map_f (T1:=ceqT_eqType) (T2:=prod_eqType _ ceqT_eqType)).
by rewrite (mem_enum (T:=cfinT_finType)).
Qed.

(* -------------------------------------------------------------------- *)

Lemma of_stringI s r : of_string s = Some r -> to_string r = s.
Proof. 
  have h := to_stringK r.
  apply : (assoc_inj (U:= ceqT_eqType) _ h).
  by rewrite stringsE -map_comp (map_inj_uniq (T1:=ceqT_eqType)) ?(enum_uniq (T:=cfinT_finType)).
Qed.

Lemma inj_of_string s1 s2 r :
     of_string s1 = Some r
  -> of_string s2 = Some r
  -> s1 = s2.
Proof. by move=> /of_stringI <- /of_stringI <-. Qed.

(* -------------------------------------------------------------------- *)
Definition to_var r := 
  {| vtype := rtype; vname := to_string r |}.
 
Definition of_var (v:var) := 
  if v.(vtype) == rtype then of_string v.(vname)
  else None.

Lemma of_varP v r : of_var v = Some r <-> v.(vtype) = rtype /\ of_string v.(vname) = Some r.
Proof. by rewrite /of_var; split=> [ | []/eqP -> ?]; first case: eqP. Qed.

Lemma to_varK : pcancel to_var of_var.
Proof. by move=> ?; rewrite /to_var /of_var /= eq_refl to_stringK. Qed.

Lemma inj_to_var : injective to_var.
Proof. apply: pcan_inj to_varK. Qed.

Lemma of_varI v r : of_var v = Some r -> to_var r = v.
Proof.
  rewrite /of_var /= /to_var; case: eqP => // heq /of_stringI.
  by case: v heq => /= ?? -> <-.
Qed.

Lemma inj_of_var v1 v2 r : of_var v1 = Some r -> of_var v2 = Some r -> v1 = v2.
Proof. by move=> /of_varI <- /of_varI <-. Qed.

Definition invalid_name (s: string) : asm_error :=
  AsmErr_string ("Invalid " ++ category ++ " name: " ++ s) None.

(*
Definition of_var_e ii (v: var) :=
  match of_var v with
  | Some r => ok r
  | None => 
    let s := 
      if vtype v == rtype then ("Invalid type variable for " ++ category)%string
      else ("Invalid variable name for " ++ category ++ ": " ++ vname v)%string in
    cierror ii (Cerr_assembler (AsmErr_string s None))
  end.

Lemma of_var_eP ii v r : 
  of_var_e ii v = ok r -> of_var v = Some r.
Proof. by rewrite /of_var_e; case: of_var => // ? [<-]. Qed.

Lemma of_var_eI ii v r : of_var_e ii v = ok r -> to_var r = v.
Proof. by move => /of_var_eP /of_varI. Qed.

Lemma inj_of_var_e ii v1 v2 r:
  of_var_e ii v1 = ok r -> of_var_e ii v2 = ok r -> v1 = v2.
Proof. by move => /of_var_eP h1 /of_var_eP; apply: inj_of_var. Qed.
*)
End Section.

Class asm_extra_op := 
  { set0_instr : wsize -> expr.instruction }.

Class asm_extra (reg xreg rflag cond asm_op : Type) := 
  { _asm   :> asm reg xreg rflag cond asm_op
  ; _extra :> asm_extra_op }.

Section AsmOp.

Context {reg xreg rflag cond asm_op : Type}
        {ad:arch_decl reg xreg cond asm_op} 
        {aod:asm_op_decl (arch:=ad) asm_op}
        {aeo:asm_extra_op}.

Definition expr_implicite_arg (i: implicite_arg) := 
  match i with 
  | IArflag r => expr.IArflag (to_var r)
  | IAreg   r => expr.IArflag (to_var r)
  end.

Definition expr_arg_desc (ad:arg_desc) := 
  match ad with
  | ADImplicit ia => expr.ADImplicit (expr_implicite_arg ia)
  | ADExplicit _ n ox => expr.ADExplicit n (omap (to_var (tS:=_)) ox)
  end.

Definition get_instr instr := 
 let id := instr_desc instr in
 {| expr.str      := id.(id_str_jas)
  ; expr.tin      := id.(id_tin)
  ; expr.i_in     := map expr_arg_desc id.(id_in)
  ; expr.i_out    := map expr_arg_desc id.(id_out)
  ; expr.tout     := id.(id_tout)
  ; expr.semi     := id.(id_semi)
  ; expr.tin_narr := id.(id_tin_narr)
  ; expr.wsizei   := id.(id_wsize)
  ; expr.i_safe   := id.(id_safe) |}.

Global Instance asm_opI : expr.asmOp asm_op := 
  {| expr._eqT := _
   ; expr.asm_op_instr := get_instr
   ; expr.set0_instr := set0_instr |}.

End AsmOp.

