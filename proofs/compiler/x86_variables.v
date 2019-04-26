From mathcomp Require Import all_ssreflect all_algebra.
Require Import low_memory x86_sem compiler_util.
Import Utf8 String.
Import all_ssreflect.
Import xseq expr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition string_of_register r :=
  match r with
  | RAX => "RAX"
  | RCX => "RCX"
  | RDX => "RDX"
  | RBX => "RBX"
  | RSP => "RSP"
  | RBP => "RBP"
  | RSI => "RSI"
  | RDI => "RDI"
  | R8  => "R8"
  | R9  => "R9"
  | R10 => "R10"
  | R11 => "R11"
  | R12 => "R12"
  | R13 => "R13"
  | R14 => "R14"
  | R15 => "R15"
  | RIP => "RIP"
  end%string.

Definition string_of_xmm_register r : string :=
  match r with
  | XMM0 => "XMM0"
  | XMM1 => "XMM1"
  | XMM2 => "XMM2"
  | XMM3 => "XMM3"
  | XMM4 => "XMM4"
  | XMM5 => "XMM5"
  | XMM6 => "XMM6"
  | XMM7 => "XMM7"
  | XMM8 => "XMM8"
  | XMM9 => "XMM9"
  | XMM10 => "XMM10"
  | XMM11 => "XMM11"
  | XMM12 => "XMM12"
  | XMM13 => "XMM13"
  | XMM14 => "XMM14"
  | XMM15 => "XMM15"
  end.

Definition string_of_rflag (rf : rflag) : string :=
  match rf with
 | CF => "CF"
 | PF => "PF"
 | ZF => "ZF"
 | SF => "SF"
 | OF => "OF"
 | DF => "DF"
 end%string.

Definition regs_strings :=
  Eval compute in [seq (string_of_register x, x) | x <- registers].

Lemma regs_stringsE : regs_strings =
  [seq (string_of_register x, x) | x <- registers].
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Definition xmm_regs_strings :=
  Eval compute in [seq (string_of_xmm_register x, x) | x <- xmm_registers].

Lemma xmm_regs_stringsE : xmm_regs_strings =
  [seq (string_of_xmm_register x, x) | x <- xmm_registers].
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Definition rflags_strings :=
  Eval compute in [seq (string_of_rflag x, x) | x <- rflags].

Lemma rflags_stringsE : rflags_strings =
  [seq (string_of_rflag x, x) | x <- rflags].
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Definition reg_of_string (s : string) :=
  assoc regs_strings s.

(* -------------------------------------------------------------------- *)
Definition xmm_reg_of_string (s : string) :=
  assoc xmm_regs_strings s.

(* -------------------------------------------------------------------- *)
Definition rflag_of_string (s : string) :=
  assoc rflags_strings s.

(* -------------------------------------------------------------------- *)
Lemma rflag_of_stringK : pcancel string_of_rflag rflag_of_string.
Proof. by case. Qed.

Lemma reg_of_stringK : pcancel string_of_register reg_of_string.
Proof. by case. Qed.

Lemma xmm_reg_of_stringK : pcancel string_of_xmm_register xmm_reg_of_string.
Proof. by case. Qed.

Lemma inj_string_of_rflag : injective string_of_rflag.
Proof. by apply: (pcan_inj rflag_of_stringK). Qed.

Lemma inj_string_of_register : injective string_of_register.
Proof. by apply: (pcan_inj reg_of_stringK). Qed.

Lemma inj_string_of_xmm_register : injective string_of_xmm_register.
Proof. by apply: (pcan_inj xmm_reg_of_stringK). Qed.

(* -------------------------------------------------------------------- *)
Lemma inj_reg_of_string s1 s2 r :
     reg_of_string s1 = Some r
  -> reg_of_string s2 = Some r
  -> s1 = s2.
Proof. by rewrite /reg_of_string !regs_stringsE; apply: inj_assoc. Qed.

(* -------------------------------------------------------------------- *)
Lemma xmm_reg_of_stringI s r :
  xmm_reg_of_string s = Some r →
  string_of_xmm_register r = s.
Proof.
  have := xmm_reg_of_stringK r.
  move => /assoc_inj. apply. done.
Qed.

(* -------------------------------------------------------------------- *)
Lemma inj_xmm_reg_of_string s1 s2 r :
     xmm_reg_of_string s1 = Some r
  -> xmm_reg_of_string s2 = Some r
  -> s1 = s2.
Proof. by rewrite /xmm_reg_of_string !xmm_regs_stringsE; apply: inj_assoc. Qed.

(* -------------------------------------------------------------------- *)
Lemma inj_rflag_of_string s1 s2 rf :
     rflag_of_string s1 = Some rf
  -> rflag_of_string s2 = Some rf
  -> s1 = s2.
Proof. by rewrite /rflag_of_string !rflags_stringsE; apply: inj_assoc. Qed.

(* -------------------------------------------------------------------- *)

Definition var_of_register r := 
  {| vtype := sword64 ; vname := string_of_register r |}. 

Definition var_of_xmm_register r :=
  {| vtype := sword256 ; vname := string_of_xmm_register r |}.

Definition var_of_flag f := 
  {| vtype := sbool; vname := string_of_rflag f |}. 

Lemma var_of_register_inj x y :
  var_of_register x = var_of_register y →
  x = y.
Proof. by move=> [];apply inj_string_of_register. Qed.

Lemma var_of_flag_inj x y : 
  var_of_flag x = var_of_flag y →
  x = y.
Proof. by move=> [];apply inj_string_of_rflag. Qed.

Lemma var_of_register_var_of_flag r f :
  ¬ var_of_register r = var_of_flag f.
Proof. by case: r;case: f. Qed.

Definition register_of_var (v:var) : option register := 
  if v.(vtype) == sword64 then reg_of_string v.(vname)
  else None.

Lemma var_of_register_of_var v r :
  register_of_var v = Some r →
  var_of_register r = v.
Proof.
  rewrite /register_of_var /var_of_register;case:ifP => //.
  case: v => [vt vn] /= /eqP -> H;apply f_equal.
  by apply: inj_reg_of_string H; apply reg_of_stringK.
Qed.

Lemma register_of_var_of_register r :
  register_of_var (var_of_register r) = Some r.
Proof.
  rewrite /register_of_var /var_of_register /=.
  by apply reg_of_stringK.
Qed.

Definition flag_of_var (v: var) : option rflag :=
  if v.(vtype) == sbool then rflag_of_string v.(vname)
  else None.

Lemma var_of_flag_of_var v f :
  flag_of_var v = Some f →
  var_of_flag f = v.
Proof.
  rewrite /flag_of_var /var_of_flag;case:ifP => //.
  case: v => [vt vn] /= /eqP -> H; apply f_equal.
  by apply: inj_rflag_of_string H; apply rflag_of_stringK.
Qed.

Definition xmm_register_of_var (v:var) : option xmm_register :=
  if v.(vtype) == sword256 then xmm_reg_of_string v.(vname)
  else None.

Definition xmm_register_of_gvar (v:gvar) : option xmm_register :=
  xmm_register_of_var (gv v).

Lemma xmm_register_of_varI v r :
  xmm_register_of_var v = Some r →
  var_of_xmm_register r = v.
Proof.
  rewrite /xmm_register_of_var /var_of_xmm_register.
  by case: eqP => // <- /xmm_reg_of_stringI ->; case: v.
Qed.

Lemma xmm_register_of_var_of_xmm_register xr :
  xmm_register_of_var (var_of_xmm_register xr) = Some xr.
Proof. exact: xmm_reg_of_stringK. Qed.

(* -------------------------------------------------------------------- *)
Variant compiled_variable :=
| LRegister of register
| LXRegister of xmm_register
| LRFlag of rflag
.

Scheme Equality for compiled_variable.

Definition compiled_variable_eqMixin := comparableClass compiled_variable_eq_dec.
Canonical compiled_variable_eqType := EqType compiled_variable compiled_variable_eqMixin.

Definition compile_var (v: var) : option compiled_variable :=
  match register_of_var v with
  | Some r => Some (LRegister r)
  | None =>
  match xmm_register_of_var v with
  | Some r => Some (LXRegister r)
  | None =>
  match flag_of_var v with
  | Some f => Some (LRFlag f)
  | None => None
  end end end.

Lemma xmm_register_of_var_compile_var x r :
  xmm_register_of_var x = Some r →
  compile_var x = Some (LXRegister r).
Proof.
  move => h; rewrite /compile_var h.
  case: (register_of_var x) (@var_of_register_of_var x) => //.
  move => r' /(_ _ erefl) ?; subst x.
  have {h} := xmm_register_of_varI h.
  by destruct r, r'.
Qed.

Lemma compile_varI x cv :
  compile_var x = Some cv →
  match cv with
  | LRegister r => var_of_register r = x
  | LXRegister r => var_of_xmm_register r = x
  | LRFlag f => var_of_flag f = x
  end.
Proof.
  rewrite /compile_var.
  case: (register_of_var x) (@var_of_register_of_var x).
  + by move => r /(_ _ erefl) <- {x} [<-]{cv}.
  move => _.
  case: (xmm_register_of_var x) (@xmm_register_of_varI x).
  + by move => r /(_ _ erefl) <- {x} [<-]{cv}.
  move => _.
  case: (flag_of_var x) (@var_of_flag_of_var x) => //.
  by move => r /(_ _ erefl) <- {x} [<-]{cv}.
Qed.

(* -------------------------------------------------------------------- *)
(* Compilation of pexprs *)
(* -------------------------------------------------------------------- *)
Definition invalid_rflag (s: string) : asm_error :=
  AsmErr_string ("Invalid rflag name: " ++ s).

Definition invalid_register (s: string) : asm_error :=
  AsmErr_string ("Invalid register name: " ++ s).

Global Opaque invalid_rflag invalid_register.

(* -------------------------------------------------------------------- *)

Definition rflag_of_var ii (v: var) :=
  match v with
  | Var sbool s =>
    match (rflag_of_string s) with
    | Some r => ciok r
    | None => cierror ii (Cerr_assembler (invalid_rflag s))
    end
  | _ => cierror ii (Cerr_assembler (AsmErr_string "Invalid rflag type"))
  end.

Definition rflag_of_gvar ii (v:gvar) := rflag_of_var ii (gv v).

(* -------------------------------------------------------------------- *)

Definition assemble_cond ii (e: pexpr) : ciexec condt :=
  match e with
  | Pvar v =>
    Let r := rflag_of_gvar ii v in
    match r with
    | OF => ok O_ct
    | CF => ok B_ct
    | ZF => ok E_ct
    | SF => ok S_ct
    | PF => ok P_ct
    | DF => cierror ii (Cerr_assembler (AsmErr_string "Cannot branch on DF"))
    end

  | Papp1 Onot (Pvar v) =>
    Let r := rflag_of_gvar ii v in
    match r with
    | OF => ok NO_ct
    | CF => ok NB_ct
    | ZF => ok NE_ct
    | SF => ok NS_ct
    | PF => ok NP_ct
    | DF => cierror ii (Cerr_assembler (AsmErr_string "Cannot branch on ~~ DF"))
    end

  | Papp2 Oor (Pvar vcf) (Pvar vzf) =>
    Let rcf := rflag_of_gvar ii vcf in
    Let rzf := rflag_of_gvar ii vzf in
    if ((rcf == CF) && (rzf == ZF)) then
      ok BE_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (BE)"))

  | Papp2 Oand (Papp1 Onot (Pvar vcf)) (Papp1 Onot (Pvar vzf)) =>
    Let rcf := rflag_of_gvar ii vcf in
    Let rzf := rflag_of_gvar ii vzf in
    if ((rcf == CF) && (rzf == ZF)) then
      ok NBE_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (NBE)"))

  | Pif _ (Pvar vsf) (Papp1 Onot (Pvar vof1)) (Pvar vof2) =>
    Let rsf := rflag_of_gvar ii vsf in
    Let rof1 := rflag_of_gvar ii vof1 in
    Let rof2 := rflag_of_gvar ii vof2 in
    if ((rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok L_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (L)"))

  | Pif _ (Pvar vsf) (Pvar vof1) (Papp1 Onot (Pvar vof2)) =>
    Let rsf := rflag_of_gvar ii vsf in
    Let rof1 := rflag_of_gvar ii vof1 in
    Let rof2 := rflag_of_gvar ii vof2 in
    if ((rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok NL_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (NL)"))

  | Papp2 Oor (Pvar vzf)
          (Pif _ (Pvar vsf) (Papp1 Onot (Pvar vof1)) (Pvar vof2)) =>
    Let rzf := rflag_of_gvar ii vzf in
    Let rsf := rflag_of_gvar ii vsf in
    Let rof1 := rflag_of_gvar ii vof1 in
    Let rof2 := rflag_of_gvar ii vof2 in
    if ((rzf == ZF) && (rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok LE_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (LE)"))

  | Papp2 Oand
             (Papp1 Onot (Pvar vzf))
             (Pif _ (Pvar vsf) (Pvar vof1) (Papp1 Onot (Pvar vof2))) =>
    Let rzf := rflag_of_gvar ii vzf in
    Let rsf := rflag_of_gvar ii vsf in
    Let rof1 := rflag_of_gvar ii vof1 in
    Let rof2 := rflag_of_gvar ii vof2 in
    if ((rzf == ZF) && (rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok NLE_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (NLE)"))

  | _ => cierror ii (Cerr_assembler (AsmErr_cond e))
  end.

(* -------------------------------------------------------------------- *)

Definition reg_of_var ii (v: var) :=
  match v with
  | Var (sword U64) s =>
     match (reg_of_string s) with
     | Some r => ciok r
     | None => cierror ii (Cerr_assembler (invalid_register s))
     end
  | _ => cierror ii (Cerr_assembler (AsmErr_string "Invalid register type"))
  end.

Definition reg_of_vars ii (vs: seq var_i) :=
  mapM (reg_of_var ii \o v_var) vs.

Definition reg_of_gvar ii (v: gvar) := reg_of_var ii (gv v).

Lemma reg_of_var_register_of_var ii x r :
  reg_of_var ii x = ok r →
  register_of_var x = Some r.
Proof.
 by rewrite /register_of_var; case: x => -[] //= [] // x; case: reg_of_string => // r' [->].
Qed.

(* -------------------------------------------------------------------- *)
Definition scale_of_z' ii (z:pointer) :=
  match wunsigned z with
  | 1 => ok Scale1
  | 2 => ok Scale2
  | 4 => ok Scale4
  | 8 => ok Scale8
  | _ => cierror ii (Cerr_assembler (AsmErr_string "invalid scale"))
  end%Z.

(* s + e :
   s + n
   s + x
   s + y + n
   s + sc * y
   s + sc * y + n *)

Variant ofs :=
  | Ofs_const of pointer
  | Ofs_var   of var
  | Ofs_mul   of pointer & var
  | Ofs_add   of pointer & var & pointer
  | Ofs_error.

Fixpoint addr_ofs e :=
  match e with
  | Papp1 (Oword_of_int Uptr) (Pconst z) => Ofs_const (wrepr _ z)
  | Pvar  x          => Ofs_var (gv x)
  | Papp2 (Omul (Op_w Uptr)) e1 e2 =>
    match addr_ofs e1, addr_ofs e2 with
    | Ofs_const n1, Ofs_const n2 => Ofs_const (n1 * n2)%R
    | Ofs_const sc, Ofs_var   x  => Ofs_mul sc x
    | Ofs_var   x , Ofs_const sc => Ofs_mul sc x
    | _           , _            => Ofs_error
    end
  | Papp2 (Oadd (Op_w Uptr)) e1 e2 =>
    match addr_ofs e1, addr_ofs e2 with
    | Ofs_const n1, Ofs_const n2 => Ofs_const (n1 + n2)%R
    | Ofs_const n , Ofs_var   x  => Ofs_add 1%R x n
    | Ofs_var   x , Ofs_const n  => Ofs_add 1%R x n
    | Ofs_mul sc x, Ofs_const n  => Ofs_add sc  x n
    | Ofs_const n , Ofs_mul sc x => Ofs_add sc  x n
    | _           , _            => Ofs_error
    end
  | _ => Ofs_error
  end.

Definition addr_of_pexpr ii s (e: pexpr) :=
  match addr_ofs e with
  | Ofs_const z =>
    ciok (mkAddress z (Some s) Scale1 None)
  | Ofs_var x =>
    Let x := reg_of_var ii x in
    ciok (mkAddress 0%R (Some s) Scale1 (Some x))
  | Ofs_mul sc x =>
    Let x := reg_of_var ii x in
    Let sc := scale_of_z' ii sc in
    ciok (mkAddress 0%R (Some s) sc (Some x))
  | Ofs_add sc x z =>
    Let x := reg_of_var ii x in
    Let sc := scale_of_z' ii sc in
    ciok (mkAddress z (Some s) sc (Some x))
  | Ofs_error =>
    cierror ii (Cerr_assembler (AsmErr_string "Invalid address expression"))
  end.

Definition oprd_of_pexpr ii (e: pexpr) :=
  match e with
  | Papp1 (Oword_of_int sz') (Pconst z) =>
    Let _ := assert (sz' ≤ Uptr)%CMP
                    (ii, Cerr_assembler (AsmErr_string "Invalid pexpr for oprd: invalid cast")) in
    let w := sign_extend Uptr (wrepr sz' z) in
    ciok (Imm_op w)
  | Pvar v =>
    Let s := reg_of_gvar ii v in
    ciok (Reg_op s)
  | Pload sz' v e => (* FIXME: can we recognize more expression for e ? *)
(*    Let _ := 
      if sz == sz' then ok tt 
      else cierror ii (Cerr_assembler (AsmErr_string "Invalid pexpr for oprd: bad load cast")) in *)
     Let s := reg_of_var ii v in
     Let w := addr_of_pexpr ii s e in
     ciok (Adr_op w)
  | _ => cierror ii (Cerr_assembler (AsmErr_string "Invalid pexpr for oprd"))
  end.

Definition rm128_of_pexpr_error ii e : ciexec rm128 :=
  cierror ii (Cerr_assembler (AsmErr_string
  match e with
  | Some x => "rm128_of_pexpr: bad variable " ++ vname x
  | None => "rm128_of_pexpr"
  end)).

Definition rm128_of_pexpr ii (e: pexpr) : ciexec rm128 :=
  match e with
  | Pvar x =>
    if xmm_register_of_gvar x is Some r then ciok (RM128_reg r)
    else rm128_of_pexpr_error ii (Some (v_var (gv x)))
  | Pload _ v e =>
     Let s := reg_of_var ii v in
     Let w := addr_of_pexpr ii s e in
     ciok (RM128_mem w)
  | _ => rm128_of_pexpr_error ii None
  end.

Lemma assemble_cond_eq_expr ii pe pe' c :
  eq_expr pe pe' →
  assemble_cond ii pe = ok c →
  assemble_cond ii pe = assemble_cond ii pe'.
Proof.
elim: pe pe' c => [ z | b | n | x | ws x pe ih | sz x pe ih | op pe ih | op pe1 ih1 pe2 ih2 | op pes ih | t pe1 ih1 pe2 ih2 pe3 ih3 ]
  [ z' | b' | n' | x' | ws' x' pe' | sz' x' pe' | op' pe' | op' pe1' pe2' | op' pes' | t' pe1' pe2' pe3' ] // c;
  try (move/eqP -> => //).
- by case: x x' => /= -[x xi] gx [[x' xi']gx'] /andP /= [] /eqP <- /eqP <-.
- case/andP => [/eqP] <- {op'} h; move: (h) => /ih {ih} ih.
  case: op => //.
  case: pe h ih => //= -[] [] x xi gx.
  by case: pe' => //= -[] [] x' xi' gx' /andP /= [] /eqP <- /eqP <-.
- case/andP => [] /andP [/eqP] <- {op'} h1 h2; rewrite -/eq_expr in h1, h2.
  move: (h1) => /ih1 {ih1} ih1; move: (h2) => /ih2 {ih2} ih2.
  case: op => //.
  + case: pe1 h1 ih1 => // - [] // - [] // [[x xi] gx].
    case: pe1' => // - [] // - [] // [[x' xi'] gx'] /= /andP /= [] /eqP h /eqP h'; subst x' gx'.
    case: pe2 h2 ih2 => //.
    * case => // - [] // [[y yi] gy]; case: pe2' => // - [] // -[] // [[y' yi'] gy'] /= /andP [] /= /eqP h /eqP h'; subst y' gy'.
      by rewrite /rflag_of_gvar /=; case: (rflag_of_var _ _) => /=.
    move=> ? [] // - [[x1 xi1] gxi] - [] // - [[x2  xi2] gx2] [] // [] // q.
    case: pe2' => // ? p1 p2 p3;rewrite /eq_expr; case: eqP => // ?;subst.
    case: p1 p2 p3 => //= - [[x1' xi1'] gx1'] x2' q' /andP [] /andP /= [] /andP /= [] /eqP -> /eqP -> {x1}.
    case: x2' => // x2' /andP [] /= /eqP -> /eqP -> {x2}.
    case: q' => // - [] // q' /andP [_] h; rewrite -/eq_expr in h.
    case: q h => // y; case: q' => // y' /= /andP [] _ /eqP h.
    rewrite /rflag_of_gvar /= h.
    by case: (rflag_of_var _ x) => //=.
  case: pe1 h1 ih1 => // - [[x1 xi1] gx1]; case: pe1' => // x1' /andP [] _ /eqP /= h1; subst x1.
  case: pe2 h2 ih2 => //.
  + case => -[x2 xi2] gx2; case: pe2' => // x2' /= /andP [] _ /eqP /= h2; subst x2.
    rewrite /rflag_of_gvar /=.
    by case: (rflag_of_var _ (gv x2')).
  move => s a1 a2 a3; case: pe2' => //.
  case: a1 => // -[[x2 xi2] gx2] ? p1 p2 p3 /=; case: eqP => // ?;subst.
  case: p1 p2 p3 => //= x2' a2' a3' /= /andP /= [] /andP [] /andP /= [] _ /eqP h;subst x2.
  case: a2 => // - [] // - [] // -[[z1 zi1] gz1].
  case: a2' => // - [] // - [] // z' /= /andP [] /= _ /eqP h; subst z1. 
  by case: a3 => // -[[z2 zi2] gz2]; case: a3' => // z2' /andP [] /= _ /eqP h;subst z2.
move=> /andP [] /andP [] /andP []; rewrite -/eq_expr => /eqP h0 h1 h2 h3.
move: (h1) => /ih1 {ih1} ih1.
move: (h2) => /ih2 {ih2} ih2.
move: (h3) => /ih3 {ih3} ih3.
case: pe1 h1 ih1 => // -[[x1 xi1] gx1]; case: pe1' => // x1' /andP /= [] _ /eqP h;subst x1.
case: pe2 h2 ih2 => //.
+ case => [[x2 xi2] gx2]; case: pe2' => // x2' /andP /= [] _ /eqP h;subst x2.
  case: pe3 h3 ih3 => // - [] // - [] // - [[x3 xi3] gx3].
  case: pe3' => // - [] // -[] // x3' /= /andP /= [] _  /eqP h; subst x3.
  by rewrite /rflag_of_gvar /=.
case => // - [] // - [[x2 xi2] gx2].
case: pe2' => // -[] // -[] // x2' /= /andP /= [] _ /eqP h; subst x2.
case: pe3 h3 ih3 => // -[[x3 xi3] gx3].
case: pe3' => // x3' /= /andP /= [] _ /eqP h;subst x3.
by rewrite /rflag_of_gvar /=.
Qed.

Lemma addr_ofs_eq_expr pe pe' :
  eq_expr pe pe' →
  addr_ofs pe = addr_ofs pe'.
Proof.
elim: pe pe' => [ z | b | n | x | ws x pe ih | sz x pe ih | op pe ih | op pe1 ih1 pe2 ih2 | op pes ih | t pe1 ih1 pe2 ih2 pe3 ih3 ]
  [ z' | b' | n' | x' | ws' x' pe' | sz' x' pe' | op' pe' | op' pe1' pe2' | op' pes' | t' pe1' pe2' pe3' ] //;
  try (move/eqP -> => //).
- by case: x => -[x xi] gx /andP /= [] _ /eqP /= -> /=.
- move => /= /andP [] /eqP <-{op'} h. case: op => // - [] //. move /ih: (h) => {ih} ih.
  by case: pe h ih => // z; case: pe' => // z' /eqP ->.
case/andP => /andP [/eqP] <- {op'}; rewrite -/eq_expr => h1 h2.
move: (h1) => /ih1 {ih1} ih1.
move: (h2) => /ih2 {ih2} ih2.
by case: op => // - [] //; rewrite /= ih1 ih2.
Qed.

Lemma addr_of_pexpr_eq_expr ii r pe pe' a :
  eq_expr pe pe' →
  addr_of_pexpr ii r pe = ok a →
  addr_of_pexpr ii r pe = addr_of_pexpr ii r pe'.
Proof.
elim: pe pe' a => [ z | b | n | x | ws x pe ih | sz x pe ih | op pe ih | op pe1 ih1 pe2 ih2 | op pes ih | t pe1 ih1 pe2 ih2 pe3 ih3 ]
  [ z' | b' | n' | x' | ws' x' pe' | sz' x' pe' | op' pe' | op' pe1' pe2' | op' pes' | t' pe1' pe2' pe3' ] // c;
  try (move/eqP -> => //).
- by case: x => -[x xi] gx /andP [] /= _ /eqP -> /=.
- move=> /= /andP [] /eqP <- {op'}.
  move => h; move: (h) => /ih {ih} ih.
  by case: pe h ih => // z; case: pe' => // z' /eqP ->.
case/andP => /andP [/eqP] <- {op'}; rewrite -/eq_expr => h1 h2.
by case: op => // - [] //;
rewrite /addr_of_pexpr /= (addr_ofs_eq_expr h1) (addr_ofs_eq_expr h2).
Qed.

Lemma oprd_of_pexpr_eq_expr ii pe pe' o :
  eq_expr pe pe' →
  oprd_of_pexpr ii pe = ok o →
  oprd_of_pexpr ii pe = oprd_of_pexpr ii pe'.
Proof.
elim: pe pe' o => [ z | b | n | x | ws x pe ih | sz x pe ih | op pe ih | op pe1 ih1 pe2 ih2 | op pes ih | t pe1 ih1 pe2 ih2 pe3 ih3 ]
  [ z' | b' | n' | x' | ws' x' pe' | sz' x' pe' | op' pe' | op' pe1' pe2' | op' pes' | t' pe1' pe2' pe3' ] // o;
  try (move/eqP -> => //).
- by case: x => -[x xi] gx /andP [] /= _ /eqP /= -> /=.
- move=> /= /andP [] /andP [] /eqP ? /eqP hx h; rewrite -/eq_expr in h.
  case: x hx => x xi /= -> {x}.
  move: (h) => /ih {ih}.
  case: (reg_of_var _ _) => //= r ih.
  t_xrbindP => a ha _.
  by rewrite (addr_of_pexpr_eq_expr h ha).
move=> /= /andP [] /eqP <- {op'}.
move => h; move: (h) => /ih {ih} ih.
by case: pe h ih => // z; case: pe' => // z' /eqP ->.
Qed.

Lemma rm128_of_pexpr_eq_expr ii pe pe' rm :
  eq_expr pe pe' →
  rm128_of_pexpr ii pe = ok rm →
  rm128_of_pexpr ii pe = rm128_of_pexpr ii pe'.
Proof.
elim: pe pe' rm => [ z | b | n | x | ws x pe ih | sz x pe ih | op pe ih | op pe1 ih1 pe2 ih2 | op pes ih | t pe1 ih1 pe2 ih2 pe3 ih3 ]
  [ z' | b' | n' | x' | ws' x' pe' | sz' x' pe' | op' pe' | op' pe1' pe2' | op' pes' | t' pe1' pe2' pe3' ] // rm.
- by case: x => -[x xi] gx /andP [] /= _ /eqP /= ->.
move => /= /andP [] /andP [] /eqP _ /eqP <- rec.
by t_xrbindP => r -> a ok_a _ /=; rewrite (addr_of_pexpr_eq_expr rec ok_a).
Qed.
