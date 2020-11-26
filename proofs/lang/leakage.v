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
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import Psatz xseq.
Require Export array expr gen_map low_memory warray_ sem_type.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope leakage_scope with leakage.
Open Scope leakage_scope.

Inductive leak_e :=
| LEmpty : leak_e (* no leak *)
| LIdx : Z -> leak_e (* array access at given index *)
| LAdr : pointer -> leak_e (* memory access at given address *)
| LSub: (seq leak_e) -> leak_e. (* forest of leaks *)

Definition get_seq_leak_e (l : leak_e) : seq leak_e := 
match l with 
| LSub le => le
| _ => [::]
end.

Inductive leak_i : Type :=
  | Lassgn : leak_e -> leak_i
  | Lopn  : leak_e ->leak_i
  | Lcond  : leak_e -> bool -> seq leak_i -> leak_i
  | Lwhile_true : seq leak_i -> leak_e -> seq leak_i -> leak_i -> leak_i 
  | Lwhile_false : seq leak_i -> leak_e -> leak_i
  | Lfor : leak_e -> seq (seq leak_i) -> leak_i
  | Lcall : leak_e -> (funname * seq leak_i) -> leak_e -> leak_i.

Notation leak_c := (seq leak_i).

Notation leak_for := (seq leak_c) (only parsing).

Notation leak_fun := (funname * leak_c)%type.

(* ------------------------------------------------------------------------ *)
(* Leakage trees and leakage transformations. *)

Inductive leak_tr_p :=
  | LS_const of pointer 
  | LS_stk
  | LS_Add `(leak_tr_p) `(leak_tr_p) 
  | LS_Mul `(leak_tr_p) `(leak_tr_p).

(*Inductive leak_tr_const := 
  | LTleak  `(leak_e)
  | LTAdr   `(leak_tr_p).
(*  | LTSub   `(seq leak_tr_const). *)
*)

(* Leakage transformer for expressions *)
Inductive leak_e_tr :=
| LT_id (* preserve *)
| LT_remove (* remove *)
| LT_const : leak_tr_p -> leak_e_tr
| LT_subi : nat -> leak_e_tr (* projection *)
| LT_lidx : (Z -> leak_tr_p) -> leak_e_tr
| LT_map : seq leak_e_tr -> leak_e_tr (* parallel transformations *)
| LT_seq : seq leak_e_tr -> leak_e_tr
| LT_compose: leak_e_tr -> leak_e_tr -> leak_e_tr. (* compositon of transformations *)
(*| LT_var : leak_e_tr -> leak_e -> leak_e_tr
| LT_adr : Z -> Z -> leak_e_tr 
| LT_adrptr : pointer -> Z -> Z -> leak_e_tr.*)


Definition get_seq_leak_e_tr (l : leak_e_tr) : seq leak_e_tr := 
match l with 
| LT_seq le => le
| _ => [::]
end.

Fixpoint eval_leak_tr_p stk lp : pointer :=
  match lp with
  | LS_const p => p 
  | LS_stk     => stk
  | LS_Add p1 p2 => (eval_leak_tr_p stk p1 + eval_leak_tr_p stk p2)%R
  | LS_Mul p1 p2 => (eval_leak_tr_p stk p1 * eval_leak_tr_p stk p2)%R
  end.
(*
Definition eval_leak_tr_const stk trc :=
  match trc with
  | LTleak le => le
  | LTAdr  lp => LAdr (eval_leak_tr_p stk lp)
  end.
*)
Fixpoint leak_E_stk (stk:pointer) (lt : leak_e_tr) (l : leak_e) : leak_e :=
  match lt, l with
  | LT_map lts, LSub xs => LSub (map2 (leak_E_stk stk) lts xs)
  | LT_seq lts, _ => LSub (map (fun lt => leak_E_stk stk lt l) lts)
  | LT_lidx f, LIdx i => LAdr (eval_leak_tr_p stk (f i))
  | LT_const f, _     => LAdr (eval_leak_tr_p stk f)
  | LT_id, _ => l
  | LT_remove, _ => LEmpty
  | LT_subi i, LSub xs => nth LEmpty xs i
  | LT_compose lt1 lt2, _ => leak_E_stk stk lt2 (leak_E_stk stk lt1 l)
  (*| LT_adr z1 z2 , LIdx i => LAdr (wrepr U64 (i*z1+z2))
  | LT_var lte le , LEmpty => LSub [:: leak_E lte LEmpty; le]
  | LT_adrptr p1 z1 z2 , LIdx i => LAdr (p1 + (wrepr U64 (i*z1+z2)))*)
  | _, _ => LEmpty
  end.

(* LT_seq -> LT_map *)
(* LT_build -> LT_seq *)

(*Notation leak_E := (leak_E_stk stk).

Parameter l0 : leak_e.

Parameter l1 : leak_e.

Compute (leak_E (LT_build [:: LT_subi 1; LT_subi 0]) (LSub [:: l0; l1])).
*)
(* t[i] ==> LSub [ :: leak_i ; (LIdx i)])

load stk (i * scale + ofs) 
==> LSub [:: LSub[:: LSub[:: leak_i; LEmpty] ; LEmpty];  
             (LAdr (vstk + (i * scale + ofs))]]

*) 

(*
Parameter i : Z.
Parameter leak__i : leak_e.
Parameter scale : pointer.
Parameter ofs   : pointer.
Parameter vstk  : pointer.
Definition lsource := LSub [ :: leak__i ; (LIdx i)].
Definition ltarget := 
 LSub [:: LSub[:: LSub[:: leak__i; LEmpty] ; LEmpty];  
             (LAdr (vstk + ((wrepr U64 i) * scale + ofs)))].

Definition ltr_i := LT_subi 0.
Definition ltr_e := LT_remove.
Definition f1 := LT_build [:: LT_build [:: ltr_i; ltr_e]; LT_remove].

Definition f2 :=
  LT_compose (LT_subi 1) 
   (LT_lidx (fun i => 
      (LS_Add LS_stk
        (LS_Add (LS_Mul (LS_const (wrepr U64 i)) (LS_const scale)) (LS_const ofs))))).

Definition ltr := LT_build [::f1; f2].

Lemma test : leak_E_stk vstk ltr lsource = ltarget.
done.
*)

(*

Parameter ofs   : pointer.
Parameter vstk  : pointer.
Definition lsource := LEmpty. 
Definition ltarget := 
 LSub [:: LEmpty ; (LAdr (vstk + ofs))].

Definition ltr :=
  LT_build [:: LT_id; LT_const (LS_Add LS_stk (LS_const ofs))].

Lemma test : leak_E_stk vstk ltr lsource = ltarget.
done.
*)

(* Leakge transformer for instructions *)
Inductive leak_i_tr :=
| LT_iremove : leak_i_tr
| LT_ikeep : leak_i_tr
| LT_ile : leak_e_tr -> leak_i_tr  (* assign and op *)
| LT_icond : leak_e_tr -> seq leak_i_tr -> seq leak_i_tr -> leak_i_tr (* if *)
| LT_iwhile : seq leak_i_tr -> leak_e_tr -> seq leak_i_tr -> leak_i_tr (* while *)
| LT_icond_eval : seq leak_i_tr -> leak_i_tr
| LT_ifor : leak_e_tr -> seq leak_i_tr -> leak_i_tr
| LT_icall : leak_e_tr -> leak_e_tr -> leak_i_tr
| LT_ifor_unroll: seq leak_i_tr -> leak_i_tr
| LT_icall_inline: leak_c -> seq leak_i_tr -> leak_i_tr.
(*| LT_icompose : leak_i_tr -> leak_i_tr -> leak_i_tr.*)

Section Leak_I.

  Variable leak_I : leak_i -> leak_i_tr -> pointer ->  seq leak_i.

  Definition leak_Is (lts : seq leak_i_tr) (ls : seq leak_i)  (stks : seq pointer) : seq leak_i :=
    flatten (map3 leak_I ls lts stks).

  Definition leak_Iss (ltss : seq leak_i_tr) (ls : seq (seq leak_i)) (stks : seq (seq pointer)) : seq (seq leak_i) :=
    (map2 (leak_Is ltss) ls stks).

End Leak_I.

Section Leak_Call.

Variable stks : seq pointer.

Variable stkss : seq (seq pointer).

Variable leak_Fun : funname -> seq leak_i_tr.

Definition dummy_lit := Lassgn LEmpty.

Definition leak_assgn := 
(Lassgn (LSub [:: LEmpty ; LEmpty])).

Definition get_empty_leak_seq (l : seq leak_e_tr) :=
(map (fun x => LEmpty) l).

Fixpoint leak_I_stk (l : leak_i) (lt : leak_i_tr) (stk:pointer) {struct l} : seq leak_i :=
  match lt, l with
  | LT_iremove, _ => [::]
  | LT_ikeep, _ => [::l]
  | LT_ile lte, Lassgn le => [:: Lassgn (leak_E_stk stk lte le) ]
  | LT_ile lte, Lopn le   => [:: Lopn (leak_E_stk stk lte le) ]
  | LT_icond lte ltt ltf, Lcond le b lti => 
    [:: Lcond (leak_E_stk stk lte le) b (leak_Is leak_I_stk (if b then ltt else ltf) lti stks) ]
  | LT_iwhile ltis lte ltis', Lwhile_true lts le lts' lw => 
    [:: Lwhile_true (leak_Is leak_I_stk ltis lts stks)
                     (leak_E_stk stk lte le)
                     (leak_Is leak_I_stk ltis' lts' stks)
                     (head dummy_lit (leak_I_stk lw lt stk))]
  | LT_iwhile ltis lte ltis', Lwhile_false lts le => 
    [::Lwhile_false (leak_Is leak_I_stk ltis lts stks)
                     (leak_E_stk stk lte le)]
  | LT_icond_eval lts, Lcond _ _ lti => 
    leak_Is leak_I_stk lts lti stks
  | LT_icond_eval lts, Lwhile_false lti le =>
    leak_Is leak_I_stk lts lti stks
  | LT_ifor lte ltiss, Lfor le ltss => [:: Lfor (leak_E_stk stk lte le)
                                                (leak_Iss leak_I_stk ltiss ltss stkss) ]
  | LT_icall lte lte', Lcall le (f, lts) le' => [:: Lcall (leak_E_stk stk lte le)
                                                          (f, (leak_Is leak_I_stk (leak_Fun f) lts stks))
                                                          (leak_E_stk stk lte' le') ]
  | LT_ifor_unroll ltiss, Lfor le ltss => 
    flatten (map (fun l => leak_assgn :: l) (leak_Iss leak_I_stk ltiss ltss stkss))
  | LT_icall_inline lc ltc', Lcall le (f, lts) le' => 
    (map (fun x => (Lassgn (LSub [:: x; LEmpty]))) (get_seq_leak_e le) ++ 
     lc ++
     leak_Is leak_I_stk (leak_Fun f) lts stks ++
    (map (fun y => (Lassgn (LSub [:: LEmpty; y]))) (get_seq_leak_e le')))
  (*| LT_icompose lt1 lt2 => leak_I (leak_I l lt1) lt2*)
  
  | _, _ => [:: l]
  end.

End Leak_Call.

Notation leak_c_tr := (seq leak_i_tr).

Definition leak_f_tr := seq (funname * leak_c_tr).

Section Leak_Call_Imp.

Variable Fs: leak_f_tr.

Definition leak_Fun (f: funname) : leak_c_tr := odflt [::] (assoc Fs f).

End Leak_Call_Imp.














