From mathcomp Require Import all_ssreflect all_algebra.
Require Import arch_decl compiler_util lea.
Import Utf8 String.
Import all_ssreflect.
Import xseq expr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Section.

Context (rtype:stype) {T:finType} {tS : ToString rtype T}.

Definition of_string (s : string) :=
  assoc strings s.

(* -------------------------------------------------------------------- *)
Lemma to_stringK : pcancel to_string of_string.
Proof.
move=> r; rewrite /of_string stringsE; apply /assocP.
+ by rewrite -map_comp map_inj_uniq ?enum_uniq //; apply inj_to_string.
by apply: map_f; rewrite mem_enum.
Qed.

(* -------------------------------------------------------------------- *)

Lemma of_stringI s r : of_string s = Some r -> to_string r = s.
Proof. 
  have /assoc_inj := to_stringK r; apply. 
  by rewrite stringsE -map_comp map_inj_uniq ?enum_uniq.
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

Definition of_var_e ii (v: var) :=
  match of_var v with
  | Some r => ciok r
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

End Section.

Section Section.

Context {reg xreg rflag:finType} {condt: eqType} {arch : arch_decl reg xreg rflag condt}.

Definition to_reg   v : option reg_t   := of_var v.
Definition to_xreg  v : option xreg_t  := of_var v.
Definition to_rflag v : option rflag_t := of_var v.

(* -------------------------------------------------------------------- *)
Variant compiled_variable :=
| LReg   of reg_t
| LXReg  of xreg_t
| LRFlag of rflag_t
.

Definition compiled_variable_beq cv1 cv2 := 
  match cv1, cv2 with
  | LReg   r1, LReg   r2 => r1 == r2
  | LXReg  r1, LXReg  r2 => r1 == r2
  | LRFlag r1, LRFlag r2 => r1 == r2
  | _, _ => false
  end.

Lemma compiled_variable_eq_axiom : Equality.axiom compiled_variable_beq.
Proof.
  move=> [r1 | x1 | f1] [r2 | x2 | f2] /=; 
    (by constructor || by apply:(iffP idP) => [ /eqP -> | [->] ]).
Qed.

Definition compiled_variable_eqMixin     := Equality.Mixin compiled_variable_eq_axiom.
Canonical  compiled_variable_eqType      := Eval hnf in EqType compiled_variable compiled_variable_eqMixin.

Definition compile_var (v: var) : option compiled_variable :=
  match to_reg v with
  | Some r => Some (LReg r)
  | None =>
  match to_xreg v with
  | Some r => Some (LXReg r)
  | None =>
  match to_rflag v with
  | Some f => Some (LRFlag f)
  | None => None
  end end end.

(*
Lemma xmm_register_of_var_compile_var x r :
  to_reg v xmm_register_of_var x = Some r →
  compile_var x = Some (LXReg r).
Proof.
  move => h; rewrite /compile_var h.
  case: (register_of_var x) (@var_of_register_of_var x) => //.
  move => r' /(_ _ erefl) ?; subst x.
  have {h} := xmm_register_of_varI h.
  by destruct r, r'.
Qed.
*)

Lemma compile_varI x cv :
  compile_var x = Some cv →
  match cv with
  | LReg   r => to_var r = x
  | LXReg  r => to_var r = x
  | LRFlag r => to_var r = x
  end.
Proof.
  rewrite /compile_var /to_reg /to_xreg /to_rflag.
  case heqr: (of_var x) => [ r | ].
  + by move=> [<-]; apply: of_varI.
  case heqx: (of_var x) => [ r | ].
  + by move=> [<-]; apply: of_varI.
  case heqf: (of_var x) => [ r | //].
  by move=> [<-]; apply: of_varI.
Qed.

(* -------------------------------------------------------------------- *)
(* Compilation of pexprs                                                *)
(* -------------------------------------------------------------------- *)


(* -------------------------------------------------------------------- *)
(* FIXME ARM : this should be a field of arch_decl ? *)
(*
Definition assemble_cond ii (e: pexpr) : ciexec condt :=
  match e with
  | Pvar v =>
    Let r := rflag_of_var ii v.(gv) in
    match r with
    | OF => ok O_ct
    | CF => ok B_ct
    | ZF => ok E_ct
    | SF => ok S_ct
    | PF => ok P_ct
    | DF => cierror ii (Cerr_assembler (AsmErr_string "Cannot branch on DF" None))
    end

  | Papp1 Onot (Pvar v) =>
    Let r := rflag_of_var ii v.(gv) in
    match r with
    | OF => ok NO_ct
    | CF => ok NB_ct
    | ZF => ok NE_ct
    | SF => ok NS_ct
    | PF => ok NP_ct
    | DF => cierror ii (Cerr_assembler (AsmErr_string "Cannot branch on ~~ DF" None))
    end

  | Papp2 Oor (Pvar vcf) (Pvar vzf) =>
    Let rcf := rflag_of_var ii vcf.(gv) in
    Let rzf := rflag_of_var ii vzf.(gv) in
    if ((rcf == CF) && (rzf == ZF)) then
      ok BE_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (BE)" None))

  | Papp2 Oand (Papp1 Onot (Pvar vcf)) (Papp1 Onot (Pvar vzf)) =>
    Let rcf := rflag_of_var ii vcf.(gv) in
    Let rzf := rflag_of_var ii vzf.(gv) in
    if ((rcf == CF) && (rzf == ZF)) then
      ok NBE_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (NBE)" None))

  | Pif _ (Pvar vsf) (Papp1 Onot (Pvar vof1)) (Pvar vof2) =>
    Let rsf := rflag_of_var ii vsf.(gv) in
    Let rof1 := rflag_of_var ii vof1.(gv) in
    Let rof2 := rflag_of_var ii vof2.(gv) in
    if ((rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok L_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (L)" None))

  | Pif _ (Pvar vsf) (Pvar vof1) (Papp1 Onot (Pvar vof2)) =>
    Let rsf := rflag_of_var ii vsf.(gv) in
    Let rof1 := rflag_of_var ii vof1.(gv) in
    Let rof2 := rflag_of_var ii vof2.(gv) in
    if ((rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok NL_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (NL)" None))

  | Papp2 Oor (Pvar vzf)
          (Pif _ (Pvar vsf) (Papp1 Onot (Pvar vof1)) (Pvar vof2)) =>
    Let rzf := rflag_of_var ii vzf.(gv) in
    Let rsf := rflag_of_var ii vsf.(gv) in
    Let rof1 := rflag_of_var ii vof1.(gv) in
    Let rof2 := rflag_of_var ii vof2.(gv) in
    if ((rzf == ZF) && (rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok LE_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (LE)" None))

  | Papp2 Oand
             (Papp1 Onot (Pvar vzf))
             (Pif _ (Pvar vsf) (Pvar vof1) (Papp1 Onot (Pvar vof2))) =>
    Let rzf := rflag_of_var ii vzf.(gv) in
    Let rsf := rflag_of_var ii vsf.(gv) in
    Let rof1 := rflag_of_var ii vof1.(gv) in
    Let rof2 := rflag_of_var ii vof2.(gv) in
    if ((rzf == ZF) && (rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok NLE_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (NLE)" None))

  | _ => cierror ii (Cerr_assembler (AsmErr_cond e))
  end.

*)
Context (assemble_cond : instr_info -> pexpr -> ciexec cond_t).
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
(* FIXME: ARM this should be rewritten *)
Definition scale_of_z' ii (z:pointer) : ciexec nat:=
  match wunsigned z return ciexec nat with
  | 1 => ok O
  | 2 => ok 0.+1
  | 4 => ok 1.+1
  | 8 => ok 2.+1
  | _ => cierror ii (Cerr_assembler (AsmErr_string "invalid scale" None))
  end%Z.

Definition reg_of_ovar ii (x:option var_i) : ciexec (option reg_t) := 
  match x with 
  | Some x => 
    Let r := of_var_e ii x in
    ok (Some r)
  | None =>
    ok None
  end.

Definition assemble_lea ii lea := 
  Let base := reg_of_ovar ii lea.(lea_base) in
  Let offset := reg_of_ovar ii lea.(lea_offset) in
  Let scale := scale_of_z' ii lea.(lea_scale) in
  ok (Areg {|
      ad_disp := lea.(lea_disp);
      ad_base := base;
      ad_scale := scale;
      ad_offset := offset 
    |}).

Definition addr_of_pexpr (rip:var) ii sz (e: pexpr) := 
  match lea.mk_lea sz e with
  | Some lea => 
     match lea.(lea_base) with
     | Some r =>
        if r.(v_var) == rip then
          Let _ := assert (lea.(lea_offset) == None) 
            (ii, Cerr_assembler (AsmErr_string "Invalid global address" (Some e))) in
           ok (Arip lea.(lea_disp))
        else assemble_lea ii lea
      | None => 
        assemble_lea ii lea
      end 
  | None => cierror ii (Cerr_assembler (AsmErr_string "lea: not able to assemble address" (Some e)))
  end.

Definition addr_of_xpexpr rip ii sz v e :=
  addr_of_pexpr rip ii sz (Papp2 (Oadd (Op_w sz)) (Plvar v) e).

Definition xreg_of_var ii (x: var) : ciexec asm_arg :=
  if to_xreg x is Some r then ok (XReg r)
  else if to_reg x is Some r then ok (Reg r)
  else cierror ii (Cerr_assembler (AsmErr_string "Not a (x)register" None)).

Definition assemble_word rip ii (sz:wsize) max_imm (e:pexpr) :=
  match e with
  | Papp1 (Oword_of_int sz') (Pconst z) =>
    match max_imm with
    | None =>  cierror ii (Cerr_assembler (AsmErr_string "Invalid pexpr for oprd, constant not allowed" (Some e)))
    | Some sz1 =>
      let w := wrepr sz1 z in
      let w1 := sign_extend sz w in
      let w2 := zero_extend sz (wrepr sz' z) in
      Let _ := assert (w1 == w2)
                (ii, Cerr_assembler (AsmErr_string "Invalid pexpr for oprd: out of bound constant" (Some e))) in
      ciok (Imm w)
    end
  | Pvar x =>
    Let _ := assert (is_lvar x)
              (ii, Cerr_assembler (AsmErr_string "Global variables remain" (Some e))) in
    let x := x.(gv) in
    xreg_of_var ii x
  | Pload sz' v e' =>
    if (sz == sz') then
      Let w := addr_of_xpexpr rip ii Uptr v e' in
      ok (Adr w)
    else
      cierror ii (Cerr_assembler (AsmErr_string "Invalid pexpr for word: invalid Load size" (Some e)))
  | _ => cierror ii (Cerr_assembler (AsmErr_string "Invalid pexpr for word" (Some e)))
  end.

Definition arg_of_pexpr rip ii (ty:stype) max_imm (e:pexpr) :=
  match ty with
  | sbool => Let c := assemble_cond ii e in ok (Condt c)
  | sword sz => assemble_word rip ii sz max_imm e
  | sint  => cierror ii (Cerr_assembler (AsmErr_string "sint ???" (Some e)))
  | sarr _ => cierror ii (Cerr_assembler (AsmErr_string "sarr ???" (Some e)))
  end.

End Section.