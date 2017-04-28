(* * License
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

(* * Pretty-print Coq language in concrete syntax *)

(* ** Imports and abbreviations *)
open Prog
open Printer 

module F   = Format

(* ** Pretty printing
 * ------------------------------------------------------------------------ *)

let pp_bty fmt = function
  | Bool  -> F.fprintf fmt "sbool"
  | U W64 -> F.fprintf fmt "sword" 
  | U _   -> assert false
  | Int   -> F.fprintf fmt "sint"

let pp_ty fmt = function
  | Bty ty     -> pp_bty fmt ty
  | Arr(W64,i) -> F.fprintf fmt "(sarr %i)" i
  | Arr _      -> assert false

let pp_inline fmt = function
  | DoInline -> F.fprintf fmt "InlineFun"
  | NoInline -> F.fprintf fmt "DoNotInline"

let pp_ass_tag fmt = function
  | AT_keep   -> F.fprintf fmt "::="
  | AT_rename -> F.fprintf fmt ":r="
  | AT_unroll -> F.fprintf fmt ":i="
   
let infix_sop2 = function
  | Oand -> "&&"
  | Oor  -> "||"
  | Oadd -> "+"
  | Omul -> "*"
  | Osub -> "-"
  | Oeq  -> "=="
  | Oneq -> "!="
  | Olt  -> "<"
  | Ole  -> "<="
  | Ogt  -> ">"
  | Oge  -> ">="

let pp_sopn fmt sopn =
  F.fprintf fmt "%s"
    (match sopn with
    | Olnot     -> "Olnot"
    | Oxor      -> "Oxor"
    | Oland     -> "Oland"
    | Olor      -> "Olor"
    | Olsr      -> "Olsr"
    | Olsl      -> "Olsl"
    | Oif       -> "Oif"
    | Omulu     -> "Omulu"
    | Omuli     -> "Omuli"
    | Oaddcarry -> "Oaddcarry"
    | Osubcarry -> "Osubcarry"
    | Oleu      -> "Oleu"
    | Oltu      -> "Oltu"
    | Ogeu      -> "Ogeu"
    | Ogtu      -> "Ogtu"
    | Oles      -> "Oles"
    | Olts      -> "Olts"
    | Oges      -> "Oges"
    | Ogts      -> "Ogts"
    | Oeqw      -> "Oeqw"  
    )


let count = ref 0 
let vars_tbl = Hv.create 101
let fun_tbl  = Hashtbl.create 101 
let string_tbl = Hashtbl.create 101
let flist = ref []
let vlist = ref []

let reset () = 
  count := 0;
  Hv.clear vars_tbl;
  Hashtbl.clear fun_tbl;
  Hashtbl.clear string_tbl;
  flist := [];
  vlist := []
                
let new_count () =
  incr count; !count

let fresh_string s = 
  let fs = 
    if Hashtbl.mem string_tbl s then 
      let rec aux n = 
        let s = s ^ (string_of_int n) in
        if Hashtbl.mem string_tbl s then aux (n+1) 
        else s in
      aux 0 
    else s in
  Hashtbl.add string_tbl fs ();
  fs 
           
let pp_var fmt v =
  let x = try Hv.find vars_tbl v with Not_found -> assert false in
  F.fprintf fmt "%s" x

let pp_vari fmt v = pp_var fmt (L.unloc v)

let pp_funname fmt fn = 
  let x = try Hashtbl.find fun_tbl fn with Not_found -> assert false in
  F.fprintf fmt "%s" x

let rec pp_pexpr fmt = function
  | Pconst i       -> F.fprintf fmt "%s" (B.to_string i)
  | Pbool b        -> F.fprintf fmt "%a" pp_bool b
  | Pcast(W64, pe) -> F.fprintf fmt "(Pcast %a)" pp_pexpr pe
  | Pcast _        -> assert false
  | Pvar vi        -> F.fprintf fmt "%a" pp_vari vi
  | Pget(vi, pe)   -> 
    F.fprintf fmt "%a.[%a]" pp_vari vi pp_pexpr pe
  | Pload(W64, vi, pe) -> 
    F.fprintf fmt "@[<hov 2>(load@ %a@ %a)@]" pp_vari vi pp_pexpr pe
  | Pload _        ->  assert false
  | Pnot(pe)       -> F.fprintf fmt "(~~ %a)" pp_pexpr pe
  | Papp2(o, e1, e2)-> 
    Format.fprintf fmt "@[<hov 2>(%a %s@ %a)@]" 
        pp_pexpr e1 (infix_sop2 o) pp_pexpr e2


let pp_rval fmt rv =
  match rv with
  | Lnone _  -> Format.fprintf fmt "__"
  | Lvar vi  -> pp_vari fmt vi
  | Lmem(W64, vi,pe) -> 
    F.fprintf fmt "@[<hov 2>store %a@ %a@]" pp_vari vi pp_pexpr pe
  | Lmem _   -> assert false
  | Laset(vi,pe) -> F.fprintf fmt "%a.[%a]" pp_vari vi pp_pexpr pe


let pp_ret_type fmt res =
  F.fprintf fmt "[:: %a]" (pp_list "; " pp_vari) res

let pp_range fmt (dir, e1, e2) =
  match dir with
  | UpTo -> 
    F.fprintf fmt "%a to %a" pp_pexpr e1 pp_pexpr e2
  | DownTo ->
    F.fprintf fmt "%a downto %a" pp_pexpr e2 pp_pexpr e1

let dotdot = function
  | [_] -> "::"
  | _ -> ""


let rec pp_instr_r fmt instr =
  match instr with
  | Cblock c -> pp_instrs fmt c
  | Cassgn(rv,atag,pe) ->
    F.fprintf fmt "@[%a %a@ %a@]"
      pp_rval rv pp_ass_tag atag pp_pexpr pe
  | Copn(rvs,sopn,pes) ->
    begin match sopn, rvs, pes with
    | Olnot, [x], [e] -> 
      F.fprintf fmt "@[ %a :=@ ! %a@]" pp_rval x pp_pexpr e
    | Oxor, [x], [e1; e2] ->
      F.fprintf fmt "@[ %a :=@ %a ^ %a @]" pp_rval x pp_pexpr e1 pp_pexpr e2
    | Oland, [x], [e1; e2] ->
      F.fprintf fmt "@[ %a :=@ %a & %a @]" pp_rval x pp_pexpr e1 pp_pexpr e2
    | Olor, [x], [e1; e2] ->
      F.fprintf fmt "@[ %a :=@ %a | %a @]" pp_rval x pp_pexpr e1 pp_pexpr e2
    | Olsl, [x], [e1; e2] ->
      F.fprintf fmt "@[ %a :=@ %a << %a @]" pp_rval x pp_pexpr e1 pp_pexpr e2
    | Olsr, [x], [e1; e2] ->
      F.fprintf fmt "@[ %a :=@ %a >> %a @]" pp_rval x pp_pexpr e1 pp_pexpr e2
    | Oif, [x], [e1; e2; e3] ->
      F.fprintf fmt "@[ %a :=@ %a ? %a : %a@]" 
        pp_rval x pp_pexpr e1 pp_pexpr e2 pp_pexpr e3 
    | Omuli, [x], [e1; e2] ->
      F.fprintf fmt "@[ %a :=@ %a * %a @]" pp_rval x pp_pexpr e1 pp_pexpr e2
    | Omulu, [x1; x2], [e1; e2] ->
      F.fprintf fmt "@[ [p %a, %a] :=@ %a * %a @]" 
        pp_rval x1 pp_rval x2 pp_pexpr e1 pp_pexpr e2
    | Oaddcarry, [x1; x2], [e1; e2; c] ->
      F.fprintf fmt "@[ [p %a, %a] :=@ ++(%a, %a, %a) @]" 
        pp_rval x1 pp_rval x2 pp_pexpr e1 pp_pexpr e2 pp_pexpr c
    | Osubcarry, [x1; x2], [e1; e2; c] ->
      F.fprintf fmt "@[ [p %a, %a] :=@ --(%a, %a, %a) @]" 
        pp_rval x1 pp_rval x2 pp_pexpr e1 pp_pexpr e2 pp_pexpr c
    | _, _, _ -> 
      F.fprintf fmt "@[Copn [:: %a]@ %a [:: %a]@]"
        (pp_list ";@ " pp_rval) rvs 
        pp_sopn sopn
        (pp_list ";@ " pp_pexpr) pes 
    end    
  | Cif(pe,instrs_if,instrs_else) ->
    begin match instrs_else with
    | [] ->
      F.fprintf fmt "@[<v>If %a then {%s@   @[<v>%a@]@ }@]"
        pp_pexpr pe (dotdot instrs_if) pp_instrs instrs_if 
    | _ ->
      F.fprintf fmt 
        "@[<v>If %a then {%s@   @[<v>%a@]@ } else {%s@   @[<v>%a@]@ }@]"
        pp_pexpr pe (dotdot instrs_if) pp_instrs instrs_if 
        (dotdot instrs_else) pp_instrs instrs_else
    end 
  | Cfor(vi,rng,instrs) ->
    F.fprintf fmt "@[<v>For %a from %a do {%s@   @[<v>%a@]@ }@]"
      pp_vari vi pp_range rng (dotdot instrs) pp_instrs instrs
  | Cwhile(c, pe, c') ->
    F.fprintf fmt 
      "@[<v>While {%s@   @[<v>%a@]@ } in %a do {%s@   @[<v>%a@]@ }@]"
      (dotdot c) pp_instrs c
      pp_pexpr pe 
      (dotdot c') pp_instrs c'
  | Ccall(inl,rvs,fname,pes) ->
    F.fprintf fmt "@[Ccall %a [:: %a] %a [:: %a]@]"
      pp_inline inl
      (pp_list "; " pp_rval) rvs
      pp_funname fname
      (pp_list "; " pp_pexpr) pes


and pp_instr fmt instr = 
  pp_instr_r fmt instr.i_desc 

and pp_instrs fmt instrs =
  pp_list ";@ " pp_instr fmt instrs

let preprocess fd =
  let s = fresh_string fd.f_name.fn_name in
  let n = new_count () in
  flist := (s,n) :: !flist;
  Hashtbl.add fun_tbl fd.f_name s;
  let vars = vars_fc fd in
  let vtbl = Hashtbl.create 101 in
  let add_var v = 
    let s = 
      try Hashtbl.find vtbl (v.v_name, v.v_ty)
      with Not_found ->
        let s = fresh_string v.v_name in 
        Hashtbl.add vtbl (v.v_name, v.v_ty) s;
        vlist := (s, v.v_ty) :: !vlist;
        s in
    Hv.add vars_tbl v s in
  Sv.iter add_var vars


let pp_fundef fmt fd =
  F.fprintf fmt 
   "@[<v>MkFun 1%%positive @[[:: %a]@] {%s@   @[<v>%a@]@ }%%P@ %a@]"
    (pp_list ";@ " pp_var) fd.f_args
    (dotdot fd.f_body)
    pp_instrs fd.f_body
    pp_ret_type  fd.f_ret

let pp_named_fun fmt fd =
  F.fprintf fmt "@[<v>(%a,@ %a)@]" pp_funname fd.f_name pp_fundef fd

let pp_prefix fmt () = 
  F.fprintf fmt "@[<v>From mathcomp Require Import all_ssreflect.@ ";
  F.fprintf fmt "Require Import prog_notation sem.@ ";
  F.fprintf fmt "Import ZArith type expr var seq.@ @ ";
  F.fprintf fmt "Open Scope string_scope.@ ";
  F.fprintf fmt "Open Scope Z_scope.@ @ @ @]"

let pp_notation fmt () = 
  let pp_fun fmt (s,i) = 
    F.fprintf fmt "Notation %s = %i%%positive" s i in
  let pp_var fmt (s, ty) = 
    F.fprintf fmt 
     "Notation %s = (VarI {vtype := %a; vname = \"%s\" } 1%%positive)."
     s pp_ty ty s in
  F.fprintf fmt "@[<v>%a@ %a@ @ @]"
    (pp_list "@ " pp_fun) !flist
    (pp_list "@ " pp_var) !vlist

let pp_prog fmt prog =
  reset ();
  List.iter preprocess prog;

  pp_prefix fmt ();
  pp_notation fmt ();
  F.fprintf fmt "@[<v>Definition program := [::@   @[<v>%a@]]@]."
      (pp_list ";@ @ " pp_named_fun) prog
