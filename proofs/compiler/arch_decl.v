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
Require oseq.
Require Import ZArith
utils
strings wsize
memory_model
(* word *)
global
oseq
Utf8
Relation_Operators
sem_type.

(* Import Memory. *)

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ==================================================================== *)
Definition label := positive.
Definition remote_label := (funname * label)%type.

(* Indirect jumps use labels encoded as pointers: we assume such an encoding exists.
  The encoding and decoding functions are parameterized by a domain:
  they are assumed to succeed on this domain only.
*)
Parameter encode_label : seq remote_label → remote_label → option pointer.
Parameter decode_label : seq remote_label → pointer → option remote_label.
Axiom decode_encode_label : ∀ dom lbl, obind (decode_label dom) (encode_label dom lbl) = Some lbl.
Axiom encode_label_dom : ∀ dom lbl, lbl \in dom → encode_label dom lbl ≠ None.

(* ==================================================================== *)

Class arch_decl (register simd_register rflag:finType) (condt: eqType) := { 
  string_of_register : register -> string;
  string_of_simd_register : simd_register -> string;
  string_of_rflag : rflag -> string;
  string_of_condt : condt -> string;
}.

Section DECL.
  
Context {register simd_register rflag:finType} {condt: eqType}.
Context {arch : arch_decl register simd_register rflag condt}.

Definition register_t {_:arch_decl register simd_register rflag condt} := register.
Definition simd_register_t {_:arch_decl register simd_register rflag condt} := simd_register.
Definition rflag_t {_:arch_decl register simd_register rflag condt} := rflag.
Definition cond_t {_:arch_decl register simd_register rflag condt} := condt.

(* -------------------------------------------------------------------- *)
(* disp + base + scale × offset *)
Record reg_address : Type := mkAddress {
  ad_disp   : pointer;
  ad_base   : option register_t;
  ad_scale  : nat;
  ad_offset : option register_t;
}.

Inductive address := 
  | Areg of reg_address
  | Arip of pointer.  
   
(* -------------------------------------------------------------------- *)

Definition reg_address_beq (addr1: reg_address) addr2 :=
  match addr1, addr2 with
  | mkAddress d1 b1 s1 o1, mkAddress d2 b2 s2 o2 =>
    [&& d1 == d2, b1 == b2, s1 == s2 & o1 == o2]
  end.

Lemma reg_address_eq_axiom : Equality.axiom reg_address_beq.
Proof.
case=> [d1 b1 s1 o1] [d2 b2 s2 o2]; apply: (iffP idP) => /=.
+ by case/and4P ; do 4! move/eqP=> ->.
by case; do 4! move=> ->; rewrite !eqxx.
Qed.

Definition reg_address_eqMixin := Equality.Mixin reg_address_eq_axiom.
Canonical reg_address_eqType := EqType reg_address reg_address_eqMixin.

Definition address_beq (addr1: address) addr2 :=
  match addr1, addr2 with
  | Areg ra1, Areg ra2 => ra1 == ra2
  | Arip p1, Arip p2   => p1 == p2
  | _, _ => false
  end.

Lemma address_eq_axiom : Equality.axiom address_beq.
Proof.
 case=> [ra1 | p1] [ra2 | p2];apply: (iffP idP) => //=.
 + by move=> /eqP ->. + by move=> [->].
 + by move=> /eqP ->. + by move=> [->].
Qed.

Definition address_eqMixin := Equality.Mixin address_eq_axiom.
Canonical address_eqType := EqType address address_eqMixin.

End DECL.

Module RegMap. Section Section.
  Context {register simd_register rflag:finType} {condt: eqType}.
  Context {arch : arch_decl register simd_register rflag condt}.

  Definition map := {ffun register_t -> u64}.

  Definition set (m : map) (x : register_t) (y : u64) : map :=
    [ffun z => if (z == x) then y else m z].

End Section. End RegMap.

(* -------------------------------------------------------------------- *)

Module XRegMap. Section Section.
  Context {register simd_register rflag:finType} {condt: eqType}.
  Context {arch : arch_decl register simd_register rflag condt}.

  Definition map := {ffun simd_register_t -> u256 }.

  Definition set (m : map) (x : simd_register_t) (y : u256) : map :=
    [ffun z => if (z == x) then y else m z].
End Section. End XRegMap.

(* -------------------------------------------------------------------- *)

Module RflagMap. Section Section.
  Context {register simd_register rflag:finType} {condt: eqType}.
  Context {arch : arch_decl register simd_register rflag condt}.

  Variant rflagv := Def of bool | Undef.

  Definition map := {ffun rflag_t -> rflagv}.

  Definition set (m : map) (x : rflag_t) (y : bool) : map :=
    [ffun z => if (z == x) then Def y else m z].

  Definition oset (m : map) (x : rflag_t) (y : rflagv) : map :=
    [ffun z => if (z == x) then y else m z].

  Definition update (m : map) (f : rflag_t -> option rflagv) : map :=
    [ffun rf => odflt (m rf) (f rf)].

End Section. End RflagMap.

(* -------------------------------------------------------------------- *)
Notation regmap   := RegMap.map.
Notation xregmap  := XRegMap.map.
Notation rflagmap := RflagMap.map.
Notation Def      := RflagMap.Def.
Notation Undef    := RflagMap.Undef.

Scheme Equality for RflagMap.rflagv.

Lemma rflagv_eq_axiom : Equality.axiom rflagv_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_rflagv_dec_bl.
  by apply: internal_rflagv_dec_lb.
Qed.

Definition rflagv_eqMixin := Equality.Mixin rflagv_eq_axiom.
Canonical rflagv_eqType := EqType _ rflagv_eqMixin.

(* -------------------------------------------------------------------- *)

Section Section.

Context {register simd_register rflag:finType} {condt: eqType}.
Context {arch : arch_decl register simd_register rflag condt}.

Variant asm_arg : Type :=
  | Condt  of cond_t
  | Imm ws of word ws
  | Reg    of register_t
  | Adr    of address
  | XReg   of simd_register_t.

Notation asm_args := (seq asm_arg).

Variant implicite_arg : Type :=
  | IArflag of rflag_t
  | IAreg   of register_t.

Variant arg_desc :=
| ADImplicit  of implicite_arg
| ADExplicit  of nat & option register_t.

Definition E n := ADExplicit n None.

Definition asm_arg_beq (a1 a2:asm_arg) :=
  match a1, a2 with
  | Condt t1, Condt t2 => t1 == t2
  | Imm sz1 w1, Imm sz2 w2 => (sz1 == sz2) && (wunsigned w1 == wunsigned w2)
  | Reg r1, Reg r2 => r1 == r2
  | Adr a1, Adr a2 => a1 == a2
  | XReg r1, XReg r2 => r1 == r2
  | _, _ => false
  end.

Definition Imm_inj sz sz' w w' (e: @Imm sz w = @Imm sz' w') :
  ∃ e : sz = sz', eq_rect sz (λ s, (word s)) w sz' e = w' :=
  let 'Logic.eq_refl := e in (ex_intro _ erefl erefl).

Lemma asm_arg_eq_axiom : Equality.axiom asm_arg_beq.
Proof.
  case => [t1 | sz1 w1 | r1 | a1 | xr1] [t2 | sz2 w2 | r2 | a2 | xr2]; apply: (iffP idP) => //=.
  1, 5, 7, 9, 11: by move => /eqP ->.
  1, 4-7: by case => ->.
  + by move=> /andP [] /eqP ? /eqP; subst => /wunsigned_inj ->.
  by move=> /Imm_inj [? ];subst => /= ->;rewrite !eqxx.
Qed.

Definition asm_arg_eqMixin := Equality.Mixin asm_arg_eq_axiom.
Canonical asm_arg_eqType := EqType asm_arg asm_arg_eqMixin.

(* -------------------------------------------------------------------- *)
(* Writing a large word to register or memory *)
(* When writing to a register, depending on the instruction,
  the most significant bits are either preserved or cleared. *)
Variant msb_flag := MSB_CLEAR | MSB_MERGE.
Scheme Equality for msb_flag.

Lemma msb_flag_eq_axiom : Equality.axiom msb_flag_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_msb_flag_dec_bl.
  by apply: internal_msb_flag_dec_lb.
Qed.

Definition msb_flag_eqMixin := Equality.Mixin msb_flag_eq_axiom.
Canonical msb_flag_eqType := EqType msb_flag msb_flag_eqMixin.

(* -------------------------------------------------------------------- *)

Definition check_arg_dest (ad:arg_desc) (ty:stype) :=
  match ad with
  | ADImplicit _ => true
  | ADExplicit _ _ => ty != sbool
  end.

Inductive pp_asm_op_ext :=
  | PP_error
  | PP_name
  | PP_iname of wsize
  | PP_iname2 of wsize & wsize
  | PP_viname of velem & bool (* long *)
  | PP_viname2 of velem & velem (* source and target element sizes *)
  | PP_ct of asm_arg.

Record pp_asm_op := mk_pp_asm_op {
  pp_aop_name : string;
  pp_aop_ext  : pp_asm_op_ext;
  pp_aop_args : seq (wsize * asm_arg);
}.

Variant safe_cond :=
  | NotZero of wsize & nat. (* the nth argument of size sz is not zero *)

Record instr_desc_t := mk_instr_desc {
  (* Info for x86 sem *)
  id_msb_flag : msb_flag;
  id_tin      : seq stype;
  id_in       : seq arg_desc;
  id_tout     : seq stype;
  id_out      : seq arg_desc;
  id_semi     : sem_prod id_tin (exec (sem_tuple id_tout));
  id_check    : list asm_arg -> bool;
  id_nargs    : nat;
  (* Info for jasmin *)
  id_eq_size  : (size id_in == size id_tin) && (size id_out == size id_tout);
  id_max_imm  : option wsize;
  id_tin_narr : all is_not_sarr id_tin;
  id_str_jas  : unit -> string;
  id_check_dest : all2 check_arg_dest id_out id_tout;
  id_safe     : seq safe_cond;
  id_wsize    : wsize;  (* ..... *)
  id_pp_asm   : asm_args -> pp_asm_op;
}.

End Section.
