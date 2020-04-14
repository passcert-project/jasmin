open Prog

val fill_in_missing_names : 'info Prog.func -> 'info Prog.func

module X64 : sig
  (* val rsp : var *)
  val allocatables : Sv.t
  val callee_save  : Sv.t

  val flags : var list
  val all_registers : var list
end

val split_live_ranges : unit func list -> unit func list

type reg_oracle_t = {
    ro_to_save: var list;  (* TODO: allocate them in the stack rather than push/pop *)
    ro_rsp: var option;
    ro_return_address: var option;
  }

(** Returns:
  - the input function with variables turned into registers
  - the set of killed registers (see note below)
  - a free register in which the stack pointer can be saved; only when asked
  - a free register for the return address; only for subroutines

Note: Export functions can freely use caller-saved registers: they are not
reported as killed. Subroutines report ALL killed registers.

 *)
val alloc_prog : (Var0.Var.var -> var) -> (call_conv -> 'a -> bool) ->
 ('a * 'info func) list ->
 ('a * reg_oracle_t * unit func) list
 * (var -> Sv.t)
 * (i_loc -> var option)
