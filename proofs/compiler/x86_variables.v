From mathcomp Require Import all_ssreflect all_algebra.
Require Import arch_decl compiler_util asmexpr x86_decl.
Import Utf8 String.
Import all_ssreflect.
Import xseq expr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
(* Compilation of pexpr to condt                                        *)
(* -------------------------------------------------------------------- *)

Definition assemble_cond ii (e: pexpr) : ciexec cond_t :=
  match e with
  | Pvar v =>
    Let r := of_var_e ii v.(gv) in
    match r with
    | OF => ok O_ct
    | CF => ok B_ct
    | ZF => ok E_ct
    | SF => ok S_ct
    | PF => ok P_ct
    | DF => cierror ii (Cerr_assembler (AsmErr_string "Cannot branch on DF" None))
    end

  | Papp1 Onot (Pvar v) =>
    Let r := of_var_e ii v.(gv) in
    match r with
    | OF => ok NO_ct
    | CF => ok NB_ct
    | ZF => ok NE_ct
    | SF => ok NS_ct
    | PF => ok NP_ct
    | DF => cierror ii (Cerr_assembler (AsmErr_string "Cannot branch on ~~ DF" None))
    end

  | Papp2 Oor (Pvar vcf) (Pvar vzf) =>
    Let rcf := of_var_e ii vcf.(gv) in
    Let rzf := of_var_e ii vzf.(gv) in
    if ((rcf == CF) && (rzf == ZF)) then
      ok BE_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (BE)" None))

  | Papp2 Oand (Papp1 Onot (Pvar vcf)) (Papp1 Onot (Pvar vzf)) =>
    Let rcf := of_var_e ii vcf.(gv) in
    Let rzf := of_var_e ii vzf.(gv) in
    if ((rcf == CF) && (rzf == ZF)) then
      ok NBE_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (NBE)" None))

  | Pif _ (Pvar vsf) (Papp1 Onot (Pvar vof1)) (Pvar vof2) =>
    Let rsf := of_var_e ii vsf.(gv) in
    Let rof1 := of_var_e ii vof1.(gv) in
    Let rof2 := of_var_e ii vof2.(gv) in
    if ((rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok L_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (L)" None))

  | Pif _ (Pvar vsf) (Pvar vof1) (Papp1 Onot (Pvar vof2)) =>
    Let rsf := of_var_e ii vsf.(gv) in
    Let rof1 := of_var_e ii vof1.(gv) in
    Let rof2 := of_var_e ii vof2.(gv) in
    if ((rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok NL_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (NL)" None))

  | Papp2 Oor (Pvar vzf)
          (Pif _ (Pvar vsf) (Papp1 Onot (Pvar vof1)) (Pvar vof2)) =>
    Let rzf := of_var_e ii vzf.(gv) in
    Let rsf := of_var_e ii vsf.(gv) in
    Let rof1 := of_var_e ii vof1.(gv) in
    Let rof2 := of_var_e ii vof2.(gv) in
    if ((rzf == ZF) && (rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok LE_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (LE)" None))

  | Papp2 Oand
             (Papp1 Onot (Pvar vzf))
             (Pif _ (Pvar vsf) (Pvar vof1) (Papp1 Onot (Pvar vof2))) =>
    Let rzf := of_var_e ii vzf.(gv) in
    Let rsf := of_var_e ii vsf.(gv) in
    Let rof1 := of_var_e ii vof1.(gv) in
    Let rof2 := of_var_e ii vof2.(gv) in
    if ((rzf == ZF) && (rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok NLE_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (NLE)" None))

  | _ => cierror ii (Cerr_assembler (AsmErr_cond e))
  end.

