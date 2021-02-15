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

(** This defines an example instance of the memory model.

The stack grows towards lower addresses, from the root to the bottom.

The stack is full when the “top” reaches the stack limit.

Stack frames are made of data (for local variables), meta-data (for code
introduced by the compiler) and padding (for enforcing alignment).

The pointer to the top is aligned during allocation
thanks to the introduction of enough padding.

The basic model maps each address to one bit (is this address allocated) and one
byte (the contents).

We additionally maintain two invariants:

 - the data part of each stack frame is allocated
 - the memory below the stack is free


*)

Require memory_model array type.

Import Utf8.
Import all_ssreflect all_algebra.
Import ZArith.
Import ssrZ.
Import type word utils gen_map.
Import memory_model.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma zip_nil S T (m: seq T) : zip [::] m = @ nil (S * T).
Proof. by case: m. Qed.

Lemma cut_wbase_Uptr sz :
  wbase Uptr = (wsize_size sz * CoqWord.word.modulus (nat63.+3 - (Nat.log2 (wsize_size_minus_1 sz))))%Z.
Proof. by case: sz; vm_compute. Qed.

Local Open Scope Z_scope.

Lemma wsize_size_le a b :
  (a ≤ b)%CMP →
  (wsize_size a | wsize_size b).
Proof.
  case: a; case: b => // _.
  1, 7, 12, 16, 19, 21: by exists 1.
  1, 6, 10, 13, 15: by exists 2.
  1, 5, 8, 10: by exists 4.
  1, 4, 6: by exists 8.
  1, 3: by exists 16.
  by exists 32.
Qed.

Lemma aligned_factor s n :
  s != 0 →
  reflect (∃ q, n = q * s) (n mod s == 0).
Proof.
  move => /eqP s_pos; case: eqP => /Zmod_divides => - /(_ s_pos) h; constructor.
  - case: h => c; exists c; Psatz.lia.
  case => c ?; apply: h; exists c; Psatz.lia.
Qed.

Lemma orX (a b: bool) (P: Prop) :
  (a → P) →
  (a = false → b → P) →
  a || b → P.
Proof. by case: a => // _ /(_ erefl); case: b. Qed.

(* -------------------------------------------------------------------------- *)

Module Align.

Local Notation is_align ptr ws :=
  (let w := wunsigned ptr in
  (w mod wsize_size ws == 0)%Z).

Lemma is_align_mod (ptr:pointer) sz : (wunsigned ptr mod wsize_size sz = 0)%Z -> is_align ptr sz.
Proof. by move=> /= ->. Qed.

Lemma is_align_add (ptr1 ptr2:pointer) sz : is_align ptr1 sz -> is_align ptr2 sz -> is_align (ptr1 + ptr2) sz.
Proof.
  have hn := wsize_size_pos sz.
  have hnz : wsize_size sz ≠ 0%Z by Psatz.lia.
  move => /eqP /Zmod_divides [] // p1 hptr1 /eqP /Zmod_divides [] // p2 hptr2.
  rewrite /wunsigned CoqWord.word.addwE -!/(wunsigned _) Zplus_mod hptr1 hptr2 -Zplus_mod.
  rewrite -/(wbase Uptr) (cut_wbase_Uptr sz) -Z.mul_add_distr_l.
  by rewrite (Z.mul_comm _ (CoqWord.word.modulus _)) mod_pq_mod_q // Z.mul_comm Z_mod_mult.
Qed.

Lemma is_align_m sz sz' (ptr: pointer) :
  (sz' ≤ sz)%CMP →
  is_align ptr sz →
  is_align ptr sz'.
Proof.
  have wsnz s : wsize_size s ≠ 0.
  - have := wsize_size_pos s.
    Psatz.lia.
  move => /wsize_size_le le /eqP /Z.mod_divide - /(_ (wsnz _)) /(Z.divide_trans _ _ _ le) {le} le.
  by apply/eqP/Z.mod_divide.
Qed.

Lemma is_align_mul sz j : is_align (wrepr Uptr (wsize_size sz * j)) sz.
Proof.
  have hn := wsize_size_pos sz.
  have hnz : wsize_size sz ≠ 0%Z by Psatz.lia.
  rewrite wunsigned_repr; lazy zeta.
  rewrite -/(wbase Uptr) (cut_wbase_Uptr sz).
  by rewrite (Z.mul_comm _ (CoqWord.word.modulus _)) mod_pq_mod_q // Z.mul_comm Z_mod_mult.
Qed.

Lemma is_align_no_overflow ptr sz :
  is_align ptr sz → no_overflow ptr (wsize_size sz).
Proof.
  rewrite /no_overflow => /eqP ha; apply/ZleP.
  have hn := wsize_size_pos sz.
  have hnz : wsize_size sz ≠ 0%Z by Psatz.lia.
  move: (wunsigned ptr) (wunsigned_range ptr) ha => {ptr} ptr.
  rewrite (cut_wbase_Uptr sz); set a := CoqWord.word.modulus _.
  move: (wsize_size sz) hn hnz => n hn hnz hr /Zmod_divides [] // q ?; subst ptr.
  cut (q + 1 <= a)%Z; Psatz.nia.
Qed.

Instance A : alignment :=
  Alignment is_align_add is_align_mod is_align_m is_align_no_overflow
            (@align_word_aligned Uptr).

End Align.

Lemma subxx p :
  sub p p = 0.
Proof. rewrite subE; Psatz.lia. Qed.

Lemma add_p_opp_sub_add_p (p q: pointer) (n: Z) :
  add p (- sub (add p n) q + n) = q.
Proof.
  rewrite !addE wrepr_add wrepr_opp subE wrepr_sub !wrepr_unsigned.
  ssrring.ssring.
Qed.

Corollary add_p_opp_sub_p (p q: pointer):
  add p (- sub p q) = q.
Proof.
  have := add_p_opp_sub_add_p p q 0.
  by rewrite add_0 Z.add_0_r.
Qed.

Lemma sub_add_small_L (p q: pointer) n :
  0 <= n <= wunsigned p →
  sub (add p (-n)) q = sub p q - n.
Proof.
  rewrite !addE !subE => n_range.
  rewrite wunsigned_add; first ring.
  have := wunsigned_range p.
  Psatz.lia.
Qed.

Lemma sub_add_small_R (p q: pointer) n :
  0 <= n <= wunsigned q →
  sub p (add q (-n)) = sub p q + n.
Proof.
  rewrite !subE => n_range.
  rewrite wunsigned_add; first ring.
  have := wunsigned_range q.
  Psatz.lia.
Qed.

Lemma sub_le (a b p: pointer) :
  wunsigned a <= wunsigned b ↔ sub p b <= sub p a.
Proof. rewrite !subE; Psatz.lia. Qed.

Lemma top_stack_after_alloc_bounded p ws sz :
  0 <= sz <= wunsigned p →
  wunsigned p - wunsigned (top_stack_after_alloc p ws sz) <= sz + wsize_size ws.
Proof.
  rewrite /top_stack_after_alloc /= => sz_pos.
  move: (align_word _ _) (align_word_range ws (p + wrepr Uptr (- sz))) => q.
  rewrite wunsigned_add; first Psatz.lia.
  have := wunsigned_range p.
  Psatz.lia.
Qed.

(** An example instance of the memory *)
Module MemoryI : MemoryT.

  Instance A : alignment := Align.A.

  Lemma addP p k: add p k = (p + wrepr U64 k)%R.
  Proof. done. Qed.

  Definition is_zalloc T (m: Mz.t T) (p:Z) : bool :=
    if Mz.get m p is Some _ then true else false.

  Record frame := { frame_size : Z ; frame_padding : Z }.

  Definition footprint_of_frame (f: frame) : Z :=
    frame_size f + frame_padding f.

  (** Total size of the stack, padding included *)
  Definition footprint_of_stack (frames: seq frame) :=
    foldr (λ f, Z.add (footprint_of_frame f)) 0 frames.

  (** Frames are valid when:
    - sizes are positive
    - stack does not overflow
  *)
  Definition valid_frame (f: frame) : bool :=
    (0 <=? frame_size f) && (0 <=? frame_padding f).

  Definition valid_frames (stk_limit stk_root: pointer) (frames: seq frame) :=
    all valid_frame frames && (footprint_of_stack frames <=? wunsigned stk_root - wunsigned stk_limit).

  (* The address [ptr] belongs to one stack frame *)
  Fixpoint pointer_into_stack (ptr: Z) (stk_root: pointer) (frames: seq frame) : bool :=
    if frames is f :: frames'
    then
      let: base := wunsigned stk_root - footprint_of_stack frames in
      (* pointer to this frame *)
      ((base <=? ptr) && (ptr <? base + frame_size f))
      ||
      (* pointer to an other frame *)
      pointer_into_stack ptr stk_root frames'
    else false (* no stack *).

  Record mem_ := {
    data      : Mz.t u8;
    alloc     : Mz.t unit;
    stk_root  : pointer; (* root of the stack *)
    stk_limit : pointer; (* limit of the stack *)
    frames    : seq frame; (* shape of the frames on the stack *)
    framesP   : valid_frames stk_limit stk_root frames;
    stk_allocP x : pointer_into_stack x stk_root frames → is_zalloc alloc x;
    stk_freeP x : 0 <= x < wunsigned stk_root - footprint_of_stack frames → is_zalloc alloc x = false;
  }.

  Arguments stk_allocP : clear implicits.
  Arguments stk_freeP : clear implicits.

  Definition mem := mem_.

  Definition is_alloc (m:mem) (p:pointer) (ws: wsize) :=
    all (fun i => is_zalloc m.(alloc) (wunsigned (add p i))) (ziota 0 (wsize_size ws)).

  Definition is_init (m:mem) (p:pointer) (ws: wsize) :=
    all (fun i => is_zalloc m.(data) (wunsigned (add p i))) (ziota 0 (wsize_size ws)).

  Lemma is_allocP m p ws :
    reflect (forall i, 0 <= i < wsize_size ws ->
               is_zalloc m.(alloc) (wunsigned (add p i)))
           (is_alloc m p ws).
  Proof.
    apply: equivP; first by apply allP.
    by split => h i hi; apply h; move: hi; rewrite in_ziota !zify Z.add_0_l.
  Qed.

  Lemma is_initE m p ws :
    is_init m p ws = all (fun i => is_init m (add p i) U8) (ziota 0 (wsize_size ws)).
  Proof.
    by rewrite /is_init /=; apply eq_in_all => ??; rewrite add_0 andbT.
  Qed.

  Lemma is_initP m p ws :
    reflect (forall i, 0 <= i < wsize_size ws -> is_init m (add p i) U8)
            (is_init m p ws).
  Proof.
    rewrite is_initE.
    apply: equivP; first by apply allP.
    split => h i hi.
    + by rewrite h // in_ziota !zify.
    by move: (h i) hi; rewrite in_ziota !zify Z.add_0_l /= add_0 => h1 /h1 [].
  Qed.

  Definition valid_pointer (m:mem) (p:pointer) (ws: wsize) :=
    is_align p ws && is_alloc m p ws.

  Definition uget (m:mem) (p:pointer) := odflt 0%R (Mz.get m.(data) (wunsigned p)).

  Definition uset (m:mem) (p:pointer) (w:u8) :=
    {| data      := Mz.set m.(data) (wunsigned p) w ;
       alloc     := m.(alloc);
       stk_root  := m.(stk_root);
       stk_limit := m.(stk_limit);
       frames    := m.(frames);
       framesP   := m.(framesP);
       stk_allocP   := m.(stk_allocP);
       stk_freeP   := m.(stk_freeP);
    |}.

  Definition validw m p ws := assert (valid_pointer m p ws) ErrAddrInvalid.

  Definition validrb m p ws := valid_pointer m p ws && is_init m p ws.

  Definition validr m p ws := assert (validrb m p ws) ErrAddrInvalid.

  Lemma is_align_wunsigned_add ptr ws i :
    is_align ptr ws →
    0 <= i < wsize_size ws →
    wunsigned (add ptr i) = wunsigned ptr + i.
  Proof.
    move => /is_align_no_overflow /lezP ??.
    rewrite wunsigned_add //.
    have := wunsigned_range ptr.
    Psatz.lia.
  Qed.

  Lemma sub_add m p s i t: validw m p s = ok t -> 0 <= i < wsize_size s -> sub (add p i) p = i.
  Proof.
    rewrite /validw => /assertP; rewrite /valid_pointer => /andP [] al _ hi.
    rewrite subE (is_align_wunsigned_add al hi); Psatz.lia.
  Qed.

  Lemma validw_uset m p v p' s : validw (uset m p v) p' s = validw m p' s.
  Proof. done. Qed.

  Lemma valid_pointerP m p ws :
    reflect
      (is_align p ws ∧ ∀ k, 0 <= k < wsize_size ws -> valid_pointer m (p + wrepr U64 k) U8)
      (valid_pointer m p ws).
  Proof.
    apply: (iffP andP) => - [] ali alo; split => //.
    - move => k range. rewrite /valid_pointer is_align8 /=.
      apply/is_allocP => i; change (wsize_size U8) with 1 => i_range.
      have -> : i = 0 by Psatz.lia.
      rewrite add_0.
      move/is_allocP: alo; exact.
    apply/is_allocP => i /alo /andP[] _ /is_allocP /(_ 0).
    rewrite add_0; apply.
    change (wsize_size U8) with 1; Psatz.lia.
  Qed.

  Lemma validrbP m p ws :
    reflect
      (is_align p ws ∧ ∀ k, 0 <= k < wsize_size ws -> validrb m (p + wrepr U64 k) U8)
      (validrb m p ws).
  Proof.
    apply: (iffP andP).
    + move=> [] /valid_pointerP [] ha hvp /is_initP hi; split => // k hk.
      by apply /andP; split; [apply hvp | apply hi].
    by move=> [] ha hk; split; [apply /valid_pointerP; split | apply /is_initP] => // k /hk /andP [].
  Qed.

  Lemma validrbE m p ws :
    validrb m p ws =
     is_align p ws && (all (fun k => validrb m (p + wrepr U64 k) U8) (ziota 0 (wsize_size ws))).
  Proof.
    apply (sameP (validrbP m p ws)); apply: (iffP andP) => -[].
    + by move=> ? /allP h; split => // k hk; apply h; rewrite in_ziota !zify.
    by move=> ? h;split => //; apply /allP => k hk; apply h; move: hk;rewrite in_ziota !zify.
  Qed.

  Lemma validrP m p s i t:
    validr m p s = ok t ->
    0 <= i < wsize_size s ->
    validr m (add p i) U8 = ok t.
  Proof.
    by rewrite /validr => /assertP /validrbP [] _ h /h ->; case: t.
  Qed.

  Lemma validw_validr m p s i v t k:
    validw m p s = ok t ->
    0 <= i < wsize_size s ->
    validr (uset m (add p i) v) k U8 = if add p i == k then ok t else validr m k U8.
  Proof.
    rewrite /validw /validr /validrb /valid_pointer is_align8 /=.
    case: andP => //= -[_ /is_allocP h] [<-] /h.
    rewrite /is_alloc /is_init /= add_0 andbT; case:eqP => //.
    + by move=> <- ->; rewrite /is_zalloc Mz.setP_eq.
    move=> hne ?; rewrite /is_zalloc Mz.setP_neq //.
    by apply /eqP => /wunsigned_inj heq; apply hne.
  Qed.

  Lemma setP m z1 z2 v:
    uget (uset m z1 v) z2 = if z1 == z2 then v else uget m z2.
  Proof.
    by rewrite /uget /uset /= Mz.setP (eqtype.inj_eq (@wunsigned_inj _)); case: eqP.
  Qed.

  Instance CM : coreMem Pointer mem :=
    CoreMem sub_add validw_uset validrP validw_validr setP.

  Definition read_mem (m: mem) (ptr: pointer) (ws: wsize) : exec (word ws) :=
    CoreMem.read m ptr ws.

  Definition bounded (z1 z2 z3: Z) := (z1 <=? z2) && (z2 <? z3).

  Definition write_mem (m: mem) (ptr:pointer) (ws:wsize) (v:word ws) :=
    CoreMem.write m ptr v.

  Lemma footprint_of_valid_frame f :
    valid_frame f →
    0 <= footprint_of_frame f.
  Proof.
    case: f => s e /andP /=; rewrite !zify /footprint_of_frame => /= - [] s_pos e_pos.
    Psatz.lia.
  Qed.

  Lemma footprint_of_valid_frames frames :
    all valid_frame frames →
    0 <= footprint_of_stack frames.
  Proof.
    elim: frames; first reflexivity.
    move => f frames ih /= /andP[] /footprint_of_valid_frame ok_f /ih{ih}.
    Psatz.lia.
  Qed.

  Lemma frame_size_in_footprint f :
    valid_frame f →
    0 <= frame_size f <= footprint_of_frame f.
  Proof.
    case/andP; rewrite !zify => s_pos e_pos; split; first exact: s_pos.
    rewrite /footprint_of_frame.
    Psatz.lia.
  Qed.

  Lemma stack_range ptr stk_root frames :
    all valid_frame frames →
    pointer_into_stack ptr stk_root frames →
    wunsigned stk_root - footprint_of_stack frames <= ptr ∧ ptr < wunsigned stk_root.
  Proof.
    elim: frames => // f frames ih /andP[] ok_f ok_fr /orP[]; last first.
    - move => /ih{ih} /(_ ok_fr).
      have /= := footprint_of_valid_frame ok_f.
      Psatz.lia.
    rewrite !zify => {ih}.
    have := footprint_of_valid_frames ok_fr.
    have /= := frame_size_in_footprint ok_f.
    Psatz.lia.
  Qed.

  Lemma readP m p s : read_mem m p s = CoreMem.read m p s.
  Proof. done. Qed.

  Lemma writeP m p s (v:word s): write_mem m p v = CoreMem.write m p v.
  Proof. done. Qed.

  Definition top_stack (m:mem) :=
    add m.(stk_root) (- footprint_of_stack m.(frames)).

  Definition set_alloc_aux T b (m:Mz.t T) (ptr sz:Z) :=
    foldl (fun m k => if b is Some t then Mz.set m k t else Mz.remove m k) m (ziota ptr sz).

  Definition set_alloc b (m:Mz.t unit) (ptr sz:Z) :=
    set_alloc_aux (if b then Some tt else None) m ptr sz.

  Definition clear_data (m:Mz.t u8) (ptr sz:Z) :=
    set_alloc_aux None m ptr sz.

  Lemma set_alloc_auxP (T:eqType) (b:option T) m p sz x :
    Mz.get (set_alloc_aux b m p sz) x =
      if (p <=? x) && (x <? p + sz) then b else Mz.get m x.
  Proof.
    rewrite /set_alloc_aux -in_ziota; elim: ziota m => //= i l hrec m.
    rewrite in_cons hrec orbC; case: {hrec} b => [t | ];
    by case: ifP => //= ?;rewrite /is_zalloc (Mz.setP, Mz.removeP) eq_sym; case: ifP.
  Qed.

  Lemma set_allocP b m p sz x :
    is_zalloc (set_alloc b m p sz) x =
      if (p <=? x) && (x <? p + sz) then b else is_zalloc m x.
  Proof. by rewrite /is_zalloc set_alloc_auxP; case: ifP => //; case: b. Qed.

  Lemma clear_dataP m p sz x :
    is_zalloc (clear_data m p sz) x =
      is_zalloc m x && ~~((p <=? x) && (x <? p + sz)).
  Proof. by rewrite /is_zalloc set_alloc_auxP; case: ifP; rewrite /= (andbT, andbF). Qed.

  (** Stack blocks: association list of frame pointers to frame sizes (data only) *)
  Definition stack_blocks_rec stk_root (frames: seq frame) :=
    foldr (λ f '(p, blk), let: s := footprint_of_frame f in let: q := add p (- s) in (q, q :: blk)) (stk_root, [::]) frames.

  Definition stack_blocks stk_root frames : seq pointer :=
    (stack_blocks_rec stk_root frames).2.

  Definition stack_frames (m: mem) : seq pointer :=
    stack_blocks m.(stk_root) m.(frames).

  Lemma stack_blocks_rec_fst stk_root frames :
    (stack_blocks_rec stk_root frames).1 = add stk_root (- footprint_of_stack frames).
  Proof.
    elim: frames; first by rewrite add_0.
    move => f stk /=.
    case: (stack_blocks_rec _ _) => /= _ _ ->; rewrite addC; congr (add stk_root).
    Psatz.lia.
  Qed.

  Lemma stack_blocks_rec_snd stk_root frames :
    if (stack_blocks_rec stk_root frames).2 is p :: tl
    then p = add stk_root (- footprint_of_stack frames)
    else frames = [::].
  Proof.
    elim: frames => // f fr.
    have /= := (stack_blocks_rec_fst stk_root fr).
    case: (stack_blocks_rec _ _) => /= top [] //=.
    - move => -> -> /=; rewrite addC; congr (add _); Psatz.lia.
    case => _ _ _ -> _; rewrite addC; congr (add _); Psatz.lia.
  Qed.

  (** Allocation of a fresh block. *)
  Lemma alloc_stack_framesP (m: mem) s :
    valid_frame s && (footprint_of_frame s + footprint_of_stack m.(frames) <=? wunsigned m.(stk_root) - wunsigned m.(stk_limit)) →
    valid_frames m.(stk_limit) m.(stk_root) (s :: m.(frames)).
  Proof.
    case/andP => ok_s ofs; apply/andP; split; first (apply/andP; split).
    - exact: ok_s.
    - by have /andP[? _] := m.(framesP).
    exact: ofs.
  Qed.

  Lemma alloc_stack_stk_allocP (m: mem) f x :
    pointer_into_stack x (stk_root m) (f :: frames m) →
    is_zalloc (set_alloc true (alloc m) (wunsigned m.(stk_root) - (footprint_of_frame f + footprint_of_stack m.(frames))) f.(frame_size)) x.
  Proof.
    rewrite set_allocP /pointer_into_stack -/pointer_into_stack; apply: orX => -> //.
    exact: m.(stk_allocP).
  Qed.
  Arguments alloc_stack_stk_allocP [m f] x.

  Lemma alloc_stack_stk_freeP (m: mem) f x :
    (valid_frame f && (footprint_of_frame f + footprint_of_stack (frames m) <=? wunsigned (stk_root m) - wunsigned (stk_limit m))) →
    0 <= x < wunsigned (stk_root m) - footprint_of_stack (f :: frames m) →
    is_zalloc (set_alloc true (alloc m) (wunsigned (stk_root m) - (footprint_of_frame f + footprint_of_stack (frames m))) (frame_size f)) x = false.
  Proof.
    case/andP => /footprint_of_valid_frame ok_f ok_ws /= range.
    rewrite set_allocP.
    case: ifPn; rewrite !zify; first Psatz.lia.
    move => nrange.
    apply: m.(stk_freeP).
    Psatz.lia.
  Qed.

  Definition alloc_stack (m: mem) (ws: wsize) (sz sz': Z) : exec mem :=
    let: top := align_word ws (add (top_stack m) (- (sz + sz'))) in
    let: padding := sub (top_stack m) top - sz in
    let: f := {| frame_size := sz ; frame_padding := padding |} in
    let: ok_f := valid_frame f in
    (* let: no_overflow := wunsigned m.(stk_limit) <=? wunsigned top in *)
    let: no_overflow := footprint_of_frame f + footprint_of_stack (frames m) <=? wunsigned (stk_root m) - wunsigned (stk_limit m) in
    match Sumbool.sumbool_of_bool (ok_f && no_overflow) with
    | right _ => Error ErrStack
    | left C =>
      ok
        {| data := clear_data m.(data) (wunsigned m.(stk_root) - (footprint_of_frame f + footprint_of_stack m.(frames))) f.(frame_size);
           alloc := set_alloc true m.(alloc) (wunsigned m.(stk_root) - (footprint_of_frame f + footprint_of_stack m.(frames))) f.(frame_size);
           stk_root := m.(stk_root);
           stk_limit := m.(stk_limit);
           frames := f :: m.(frames);
           framesP := alloc_stack_framesP C;
           stk_allocP x := alloc_stack_stk_allocP x;
           stk_freeP x :=  alloc_stack_stk_freeP C;
        |}
    end.

  (** Free *)
  Lemma free_stack_framesP (m: mem) :
    valid_frames (stk_limit m) (stk_root m) (behead (frames m)).
  Proof.
    have /andP[h /lezP k] := m.(framesP).
    apply/andP; split.
    - by case: {k} (frames m) h => //= ? ? /andP[].
    rewrite zify.
    have [??] := wunsigned_range m.(stk_root).
    case: (frames m) h k => // f fs /andP[] /footprint_of_valid_frame ? _ /=.
    Psatz.lia.
  Qed.

  Lemma free_stack_stk_allocP (m: mem) x :
    pointer_into_stack x (stk_root m) (behead (frames m)) →
    is_zalloc (set_alloc false (alloc m) (wunsigned (stk_root m) - footprint_of_stack (frames m)) (odflt 0 (omap footprint_of_frame (ohead (frames m))))) x.
  Proof.
    case: (frames m) m.(framesP) m.(stk_allocP) => // f frames /andP[] /= /andP[] ok_f valid_frames /lezP no_overflow /(_ x) old_allocated range.
    rewrite set_allocP.
    move: old_allocated; rewrite range orbT => /(_ erefl) ->.
    have := stack_range valid_frames range.
    case: andP => //; rewrite !zify {range}.
    Psatz.lia.
  Qed.
  Arguments free_stack_stk_allocP : clear implicits.

  Lemma free_stack_stk_freeP (m: mem) x :
    0 <= x < wunsigned (stk_root m) - footprint_of_stack (behead (frames m)) →
    is_zalloc (set_alloc false (alloc m) (wunsigned (stk_root m) - footprint_of_stack (frames m)) (odflt 0 (omap footprint_of_frame (ohead (frames m))))) x = false.
  Proof.
    move => range.
    have old_free := m.(stk_freeP) x.
    rewrite set_allocP; case: ifPn => // nrange.
    apply: old_free.
    split; first Psatz.lia.
    case: (frames m) m.(framesP) range nrange => //= f stk; first Psatz.lia.
    case/andP => /= /andP[] _ valid_frames _.
    have := footprint_of_valid_frames valid_frames.
    rewrite !zify; Psatz.lia.
  Qed.
  Arguments free_stack_stk_freeP : clear implicits.

  Definition free_stack (m: mem) : mem :=
    let sz := odflt 0 (omap footprint_of_frame (ohead m.(frames))) in
    {| data := m.(data);
       alloc := set_alloc false m.(alloc) (wunsigned m.(stk_root) - (footprint_of_stack m.(frames))) sz;
       stk_root := m.(stk_root);
       stk_limit := m.(stk_limit);
       frames := behead m.(frames);
       framesP := free_stack_framesP m;
       stk_allocP := free_stack_stk_allocP m;
       stk_freeP := free_stack_stk_freeP m;
    |}.

  (** Initial memory: empty with pre-allocated blocks.
    The stack is rooted at the higest aligned pointer below the lowest allocated address.
   *)
  Definition init_mem_alloc (s: seq (pointer * Z)) : Mz.t unit :=
    foldl (fun a pz => set_alloc true a (wunsigned pz.1) pz.2) (Mz.empty _) s.

  Definition all_above (s: seq (pointer * Z)) (stk: pointer) : bool :=
    all (λ '(p, _), wlt Unsigned stk p) s.

  Lemma init_mem_framesP stk_root :
    valid_frames 0 stk_root [::].
  Proof. apply/lezP; rewrite Z.sub_0_r; exact: (proj1 (wunsigned_range _)). Qed.

  Lemma init_mem_stk_allocP (stk_root: pointer) s x :
    false →
    is_zalloc (init_mem_alloc s) x.
  Proof. by []. Qed.

  Lemma init_mem_stk_freeP_aux s stk m :
    all_above s stk →
    ∀ x,
      0 <= x <= wunsigned stk →
      is_zalloc (foldl (λ a pz, set_alloc true a (wunsigned pz.1) pz.2) m s) x = is_zalloc m x.
  Proof.
    rewrite /all_above.
    elim: s m => //= - [p z] s ih m /andP[] /ltzP ok_p {}/ih ih x x_range.
    rewrite (ih _ _ x_range) {ih} set_allocP /=.
    move: ok_p; rewrite -/(wunsigned stk) -/(wunsigned p) => ok_p.
    case: andP => //; rewrite !zify.
    Psatz.lia.
  Qed.

  Lemma init_mem_stk_freeP s stk x :
   all_above s stk →
    0 <= x < wunsigned stk - 0 →
    is_zalloc (init_mem_alloc s) x = false.
  Proof.
    move => all_above x_range.
    rewrite /init_mem_alloc (init_mem_stk_freeP_aux (Mz.empty _) all_above) //; Psatz.lia.
  Qed.
  Arguments init_mem_stk_freeP : clear implicits.

  Definition init_mem (s: seq (pointer * Z)) (stk: pointer) : exec mem :=
    match Sumbool.sumbool_of_bool (is_align stk U256) with
    | right _ => Error ErrStack
    | left stk_align =>
    match Sumbool.sumbool_of_bool (all_above s stk) with
    | right _ => Error ErrStack
    | left stk_below =>
      ok
        {| data := Mz.empty _;
           alloc := init_mem_alloc s;
           stk_limit := 0%R;
           stk_root := stk;
           frames := [::];
           framesP := init_mem_framesP stk;
           stk_allocP := init_mem_stk_allocP stk s;
           stk_freeP p := init_mem_stk_freeP s stk p stk_below;
        |}
    end end.

  Instance M : memory mem :=
    Memory read_mem write_mem valid_pointer
           stk_root stk_limit stack_frames alloc_stack free_stack init_mem.

  Lemma top_stackE (m: mem) :
    memory_model.top_stack m = top_stack m.
  Proof.
    rewrite /memory_model.top_stack /= /stack_frames /top_stack /stack_blocks.
    have := stack_blocks_rec_snd (stk_root m) (frames m).
    case: (stack_blocks_rec _ _) => /= _ [] //.
    by move => ->; rewrite add_0.
  Qed.

  Lemma readV (m:mem) p s v: read_mem m p s = ok v -> valid_pointer m p s.
  Proof.
    rewrite /read_mem /CoreMem.read /= /validr.
    by t_xrbindP => _ /assertP /andP [].
  Qed.

  Lemma writeV m p s (v:word s):
    reflect (exists m', write_mem m p v = ok m') (valid_pointer m p s).
  Proof.
    rewrite /write_mem /CoreMem.write /= /validw.
    by (case: valid_pointer => /=; constructor) => [ | []//]; eauto.
  Qed.

  Lemma read_mem_error m p s e: read_mem m p s = Error e -> e = ErrAddrInvalid.
  Proof.
    rewrite /read_mem /CoreMem.read /= /validr /validrb; case: valid_pointer => [/=|[<-]//].
    by case: is_init => //= -[] ->.
  Qed.

  Lemma write_read8 m m' p ws (v: word ws) k :
    write_mem m p v = ok m' ->
    read_mem m' k U8 =
      let i := wunsigned k - wunsigned p in
      if (0 <=? i) && (i <? wsize_size ws) then ok (LE.wread8 v i)
      else read_mem m k U8.
  Proof. apply: CoreMem.write_read8. Qed.

  Lemma write_memE m m' p s (v:word s):
    write_mem m p v = ok m' ->
    validw m p s = ok tt /\ m' = CoreMem.uwrite m p v.
  Proof.
    by rewrite /write_mem /CoreMem.write /= /validw /assert; case:ifP => //= _ [<-].
  Qed.

  Lemma write_mem_invariant T (P: mem → T) :
    (∀ m p v, P (uset m p v) = P m) →
    ∀ m p s (v: word s) m',
      write_mem m p v = ok m' →
      P m  = P m'.
  Proof.
    move => K m p s v m' /write_memE[] _ ->.
    rewrite /CoreMem.uwrite.
    elim: (ziota _ _) m => // a q hrec m.
    by rewrite -hrec K.
  Qed.

  Lemma write_valid m m' p s (v:word s) p' s':
    write_mem m p v = ok m' ->
    valid_pointer m' p' s' = valid_pointer m p' s'.
  Proof. move => a; symmetry; move: a. exact: (@write_mem_invariant _ (λ m, valid_pointer m p' s')). Qed.

  Lemma top_stack_write_mem m p s (v: word s) m' :
    write_mem m p v = ok m' →
    top_stack m = top_stack m'.
  Proof. exact: write_mem_invariant. Qed.

  Lemma write_mem_stable m m' p s (v:word s) :
    write_mem m p v = ok m' -> stack_stable m m'.
  Proof.
    move => ok_m'; split => /=; exact: write_mem_invariant ok_m'.
  Qed.

  Lemma write_mem_zget m p s (v : word s) m' k :
    write_mem m p v = ok m' ->
    Mz.get (data m') (wunsigned k) =
      (let i := sub k p in
            if (0 <=? i) && (i <? wsize_size s) then Some (LE.wread8 v i) else Mz.get (data m) (wunsigned k)).
  Proof.
    move=> /write_memE [] /sub_add hsa -> /=.
    set i := sub k p.
    have := in_ziota 0 (wsize_size s) i.
    rewrite Z.add_0_l => <-.
    rewrite /CoreMem.uwrite /=.
    have : ∀ z : Z, z \in ziota 0 (wsize_size s) → sub (add p z) p = z.
    + by move=> z; rewrite in_ziota Z.add_0_l !zify; apply hsa.
    elim: (ziota _ _) m => //= {hsa}.
    move=> j l hrec m hsa; rewrite hrec; last first.
    + by move=> z h; apply /hsa; rewrite in_cons h orbT.
    rewrite in_cons.
    case: eqP => [<- | h ] /=; case: ifP => // ?.
    + by rewrite /i add_sub Mz.setP_eq.
    rewrite Mz.setP_neq //.
    apply /eqP => /wunsigned_inj => ?; subst k; apply h.
    by rewrite /i hsa // mem_head.
  Qed.

  Lemma write_mem_init_def m m' p s (v : word s) k :
     write_mem m p v = ok m' ->
     is_init m' k U8 =
        (let i := sub k p in
         (0 <=? i) && (i <? wsize_size s) || is_init m k U8).
  Proof.
    by rewrite /is_init /= add_0 !andbT /is_zalloc => /write_mem_zget /= ->; case: ifP.
  Qed.

  Lemma writeP_eq m m' p s (v : word s):
    write_mem m p v = ok m' ->
    read_mem m' p s = ok v.
  Proof.
    move=> hw; rewrite /read_mem /CoreMem.read /= /validr /validrb.
    rewrite (write_valid _ _ hw).
    (case: (writeV m p v); rewrite hw) => [[m1 _] /= | []]; last by eauto.
    rewrite (CoreMem.writeP_eq hw) LE.decodeK.
    have -> // : is_init m' p s.
    apply /is_initP => i hi.
    assert (h := write_mem_init_def (add p i) hw).
    have hv : valid_pointer m p s by apply /(@writeV m p _ v); exists m'.
    move: h; rewrite /is_init /= add_0 andbT => ->.
    rewrite !zify; have := (sub_add (m:= m) (p:=p) _ hi).
    by move=> h; rewrite (h tt); auto; rewrite /validw hv.
  Qed.

  Lemma writeP_neq m m' p s (v :word s) p' s':
    write_mem m p v = ok m' ->
    disjoint_range p s p' s' ->
    read_mem m' p' s' = read_mem m p' s'.
  Proof.
    rewrite /read_mem /CoreMem.read /= /validr /validrb => hw [ /ZleP hno /ZleP hno' hd].
    rewrite (write_valid p' s' hw); case:valid_pointer => //=.
    have -> : (is_init m' p' s') = (is_init m p' s').
    + apply eq_in_all => k; rewrite in_ziota !zify => hk.
      assert (h := write_mem_init_def (add p' k) hw).
      move: h; rewrite /is_init /= add_0 !andbT => ->.
      have ? := wunsigned_range p'.
      rewrite subE addE wunsigned_add; last by Psatz.lia.
      by case: andP => //; rewrite !zify; Psatz.lia.
    rewrite (CoreMem.writeP_neq hw) // => i i' hi hi'.
    rewrite !addE => heq.
    have : wunsigned (p + wrepr U64 i)%R = wunsigned (p' + wrepr U64 i')%R by rewrite heq.
    have hp := wunsigned_range p; have hp' := wunsigned_range p'.
    rewrite !wunsigned_add; Psatz.lia.
  Qed.

  Lemma read_write_any_mem m1 m1' pr szr pw szw (vw:word szw) m2 m2':
    valid_pointer m1 pr szr ->
    (∀ (w : pointer) (sz : wsize), valid_pointer m1 w sz → read_mem m1 w sz = read_mem m1' w sz) ->
    write_mem m1 pw vw = ok m2 ->
    write_mem m1' pw vw = ok m2' ->
    read_mem m2 pr szr = read_mem m2' pr szr.
  Proof.
    move=> hv hr hw hw'.
    have := write_valid _ _ hw.
    have := write_mem_init_def _ hw.
    move: hw hw'.
    rewrite !writeP /CoreMem.write; t_xrbindP => t1 hvw <- t2 hvw' <-.
    rewrite !readP /CoreMem.read /memory_model.validr /= /validr.
    have hvk : forall k, 0 <= k < wsize_size szr ->
                validr m1 (pr + wrepr U64 k) U8 = validr m1' (pr + wrepr U64 k) U8.
    + move=> k hk; case /valid_pointerP : hv => ? /(_ k hk) /hr.
      rewrite /read_mem /CoreMem.read /= /validr.
      by case: validrb; case: validrb.
    have <- : validrb (CoreMem.uwrite m1 pw vw) pr szr =
              validrb (CoreMem.uwrite m1' pw vw) pr szr.
    + rewrite !validrbE; f_equal; apply eq_in_all => k; rewrite in_ziota !zify => hk.
      have := (CoreMem.uwrite_validr8 vw (pr + wrepr U64 k)%R hvw).
      have := (CoreMem.uwrite_validr8 vw (pr + wrepr U64 k)%R hvw').
      rewrite /memory_model.validr /= (hvk _ hk).
      by move=> <-; rewrite /validr; case: validrb; case: validrb.
    rewrite /validrb => hi ->; rewrite hv /=.
    case: is_initP => //= hi1; do 2!f_equal.
    rewrite /CoreMem.uread; apply eq_map_ziota => k hk.
    case /valid_pointerP : hv => ? /(_ k hk) hvpk.
    move/hr: (hvpk).
    rewrite (CoreMem.uwrite_uget vw (add pr k) hvw) (CoreMem.uwrite_uget vw (add pr k) hvw').
    rewrite /read_mem /CoreMem.read /= -(hvk _ hk).
    rewrite !CoreMem.uread8_get.
    rewrite /validr /validrb hvpk /=.
    have := hi1 _ hk; rewrite hi // -addP.
    by (case heq: is_init => // /=; rewrite ?(orbT, orbF)) => [ _ [] | ] ->.
  Qed.

  (** Allocation *)
  Lemma footprint_of_stack_pos (m: mem) :
    0 <= footprint_of_stack m.(frames).
  Proof.
    have /andP[h _] := m.(framesP).
    exact: footprint_of_valid_frames.
  Qed.
  Arguments footprint_of_stack_pos : clear implicits.

  Lemma Zleb_succ (x y: Z) :
    (x + 1 <=? y) = (x <? y).
  Proof. case: Z.leb_spec; case: Z.ltb_spec => //; Psatz.lia. Qed.

  Lemma ass_valid m ws_stk sz sz' m' :
    alloc_stack m ws_stk sz sz' = ok m' →
    ∀ p,
    valid_pointer m' p U8 =
    valid_pointer m p U8 || between (top_stack m') sz p U8.
  Proof.
    rewrite /alloc_stack /valid_pointer; case: Sumbool.sumbool_of_bool => // h [<-] p.
    rewrite is_align8 /= /is_alloc /top_stack /= !andbT add_0.
    case/andP: h.
    set fr := {| frame_size := sz |} => ok_f /lezP no_ovf.
    rewrite set_allocP /between.
    have b_pos := wunsigned_range m.(stk_root).
    have l_pos := wunsigned_range m.(stk_limit).
    have f_pos := footprint_of_stack_pos m.
    have s_pos := footprint_of_valid_frame ok_f.
    rewrite wunsigned_add; last Psatz.lia.
    rewrite Zleb_succ.
    by case: ifP => _; rewrite (orbT, orbF).
  Qed.

  Lemma ass_fresh m ws_stk sz sz' m' :
    alloc_stack m ws_stk sz sz' = ok m' →
    ∀ p s,
      valid_pointer m p s →
      (wunsigned p + wsize_size s <= wunsigned (top_stack m') ∨ wunsigned (top_stack m') + sz <= wunsigned p).
  Proof.
    move => X; have := m.(stk_freeP); move: X.
    rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-] /= stk_fresh p s /andP[] p_align p_alloc.
    rewrite /top_stack /=.
    right. apply/lezP; case: lezP => // /Z.nle_gt X.
    rewrite -(stk_fresh (wunsigned p)).
    - by move/allP: p_alloc => /(_ 0); rewrite in_ziota /= (proj2 (Z.ltb_lt _ _) (wsize_size_pos s)) add_0 => /(_ erefl).
    split. apply wunsigned_range.
    apply: (Z.lt_le_trans _ _ _ X).
    clear X.
    case/andP: h => ok_f /lezP ovf.
    have rt_range := wunsigned_range (stk_root m).
    have l_range := wunsigned_range (stk_limit m).
    have {ok_f}/= := frame_size_in_footprint ok_f.
    move: (footprint_of_frame _) ovf => fr ovf fr_pos.
    have /andP[/footprint_of_valid_frames ok_s _] := framesP m.
    rewrite wunsigned_add; Psatz.lia.
  Qed.

  Lemma ass_init m ws_stk sz sz' m' :
    alloc_stack m ws_stk sz sz' = ok m' →
    ∀ p,
     is_init m' p U8 = is_init m p U8 && ~~between (top_stack m') sz p U8.
  Proof.
    rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-] p.
    rewrite /= /is_init /top_stack /= !andbT add_0.
    case/andP: h.
    set fr := {| frame_size := sz |} => ok_f /lezP no_ovf.
    rewrite clear_dataP /between.
    have b_pos := wunsigned_range m.(stk_root).
    have l_pos := wunsigned_range m.(stk_limit).
    have f_pos := footprint_of_stack_pos m.
    have s_pos := footprint_of_valid_frame ok_f.
    rewrite wunsigned_add; last Psatz.lia.
    by rewrite Zleb_succ.
  Qed.

  Lemma ass_read_old m ws_stk sz sz' m' :
    alloc_stack m ws_stk sz sz' = ok m' →
    ∀ p s,
    valid_pointer m p s →
    read_mem m p s = read_mem m' p s.
  Proof.
    move => ok_m' p s ok_m_p_s.
    have : valid_pointer m' p s.
    + have /valid_pointerP[ al_p_s ok_m_p_s_i ] := ok_m_p_s.
      apply/valid_pointerP; apply: (conj al_p_s) => k /ok_m_p_s_i.
      by rewrite (ass_valid ok_m') => ->.
    have hadd : forall k, 0 <= k < wsize_size s -> wunsigned (add p k) = wunsigned p + k.
    + by move=> k hk; move /valid_pointerP: ok_m_p_s => []/is_align_wunsigned_add -/(_ _ hk).
    have hfresh := ass_fresh ok_m' ok_m_p_s.
    have : is_init m p s = is_init m' p s.
    + rewrite !is_initE; apply eq_in_all => k; rewrite in_ziota !zify => hk.
      rewrite (ass_init ok_m').
      have -> : ~~ between (top_stack m') sz (add p k) U8; last by rewrite andbT.
      by rewrite /between !zify wsize8 hadd //; Psatz.lia.
    move: ok_m' hfresh.
    rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-].
    rewrite /read_mem /CoreMem.read /= /CoreMem.uread /= /validr /validrb ok_m_p_s /top_stack.
    move => /= hfresh <- -> /=.
    case heq: is_init => //=; do 2!f_equal; apply eq_map_ziota => i hi /=.
    rewrite /uget /= /clear_data set_alloc_auxP.
    case: ifP => //.
    case/andP: h hfresh.
    set fr := {| frame_size := sz |} => ok_f /lezP no_ovf.
    have b_pos := wunsigned_range m.(stk_root).
    have l_pos := wunsigned_range m.(stk_limit).
    have f_pos := footprint_of_stack_pos m.
    have s_pos := footprint_of_valid_frame ok_f.
    rewrite (hadd _ hi) !zify wunsigned_add; Psatz.lia.
  Qed.

  Lemma ass_read_new m ws_stk sz sz' m' :
    alloc_stack m ws_stk sz sz' = ok m' →
    ∀ p,
    ~valid_pointer m p U8 → valid_pointer m' p U8 →
    read_mem m' p U8 = Error ErrAddrInvalid.
  Proof.
    move=> ha p.
    rewrite (ass_valid ha) => /negP /negbTE -> /=.
    rewrite readP /CoreMem.read /= /validr /validrb (ass_init ha) => ->.
    by rewrite !andbF.
  Qed.

  Lemma ass_align m ws_stk sz sz' m' :
    alloc_stack m ws_stk sz sz' = ok m' →
    ∀ ofs s,
      (s <= ws_stk)%CMP →
      is_align (top_stack m' + wrepr U64 ofs) s = is_align (wrepr U64 ofs) s.
  Proof.
    rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-].
    rewrite /top_stack /= => ofs s hws_le.
    move: h; rewrite /top_stack => /andP[] /andP[] /= ok_f /lezP sz_pos.
    have /andP[ok_fs _] := framesP m.
    have fs_pos := footprint_of_valid_frames ok_fs.
    rewrite /footprint_of_frame /=.
    move: (footprint_of_stack _) sz_pos fs_pos => fs sz_pos fs_pos.
    have [n ws ] := wsize_size_le hws_le.
    have ws_pos := wsize_size_pos s.
    have s_pos := wsize_size_pos ws_stk.
    have n_pos : 0 < n by Psatz.nia.
    have ns_nz : n * wsize_size s ≠ 0 by Psatz.lia.
    move => al_top.
    rewrite Z.opp_add_distr Z.add_comm -addC.
    move: sz_pos al_top.
    set T := add (stk_root m) (- fs).
    rewrite Zplus_minus add_p_opp_sub_p.
    set T' := add T _.
    move => sz_pos al_top.
    have /aligned_factor[] := align_word_aligned ws_stk T'.
    + by apply/eqP.
    rewrite /wunsigned word.addwE => t' eq_t'.
    rewrite -/(wbase U64).
    rewrite (cut_wbase_Uptr ws_stk) ws.
    rewrite -(Z.mul_assoc n) (Z.mul_comm (wsize_size s)) (Z.mul_assoc n).
    rewrite mod_pq_mod_q //.
    + by rewrite Z.add_mod // eq_t' ws Z.mul_assoc Z.mod_mul // Z.add_0_l Z.mod_mod.
    set q := (_ - _)%nat.
    have /ltzP := word.modulus_gt0 q.
    change 0%R with 0%Z.
    Psatz.nia.
  Qed.

  Lemma ass_root m ws_stk sz sz' m' :
    alloc_stack m ws_stk sz sz' = ok m' →
    stack_root m' = stack_root m.
  Proof. by rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-]. Qed.

  Lemma ass_limit m ws_stk sz sz' m' :
    alloc_stack m ws_stk sz sz' = ok m' →
    stack_limit m' = stack_limit m.
  Proof. by rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-]. Qed.

  Lemma ass_frames m ws_stk sz sz' m' :
    alloc_stack m ws_stk sz sz' = ok m' →
    stack_frames m' = top_stack_after_alloc (top_stack m) ws_stk (sz + sz') :: stack_frames m.
  Proof.
    rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-] /=.
    rewrite /stack_frames /=.
    rewrite {1}/stack_blocks /=.
    case heq: (stack_blocks_rec _ _) => [p blk].
    rewrite /stack_blocks heq /=.
    rewrite {1}/top_stack -stack_blocks_rec_fst heq /=.
    congr cons.
    rewrite /top_stack_after_alloc.
    move: (align_word _ _) => q.
    rewrite /footprint_of_frame /=.
    by rewrite Zplus_minus add_p_opp_sub_p.
  Qed.

  Lemma alloc_stackP m m' ws_stk sz sz' :
    alloc_stack m ws_stk sz sz' = ok m' -> alloc_stack_spec m ws_stk sz sz' m'.
  Proof.
    move => o.
    split; rewrite ?top_stackE.
    - exact: ass_read_old o.
    - exact: ass_read_new o.
    - exact: ass_valid o.
    - exact: ass_align o.
    - exact: ass_fresh o.
    - exact: ass_root o.
    - exact: ass_limit o.
    exact: ass_frames o.
  Qed.

  Lemma first_frameE (m: mem) :
    odflt 0 (omap footprint_of_frame (ohead (frames m))) = wunsigned (top_stack (free_stack m)) - wunsigned (top_stack m).
  Proof.
    rewrite /top_stack /=.
    have /andP[] := framesP m.
    case: (frames m) => /=.
    + rewrite add_0; Psatz.lia.
    move => f fr /andP[] ok_f ok_fr /lezP noovf.
    have ff := footprint_of_valid_frame ok_f.
    have fs := footprint_of_valid_frames ok_fr.
    have rr := wunsigned_range (stk_root m).
    have lr := wunsigned_range (stk_limit m).
    rewrite !wunsigned_add; Psatz.lia.
  Qed.

  Lemma wunsigned_top_stack m :
    wunsigned (top_stack m) = wunsigned (stk_root m) - footprint_of_stack (frames m).
  Proof.
    have /andP[ /footprint_of_valid_frames ? /lezP h ] := framesP m.
    rewrite /top_stack wunsigned_add //.
    have := wunsigned_range (stk_root m).
    have := wunsigned_range (stk_limit m).
    Psatz.lia.
  Qed.

  Lemma fss_valid m p :
    valid_pointer (free_stack m) p U8 = valid_pointer m p U8 && ~~ pointer_range (top_stack m) (top_stack (free_stack m)) p.
  Proof.
    rewrite /valid_pointer /=.
    rewrite Z.mod_1_r eqxx /=.
    rewrite /is_alloc /= add_0 !andbT set_allocP.
    set B := (X in if X then _ else _).
    suff -> : B = pointer_range (top_stack m) (top_stack (free_stack m)) p.
    + by case: ifP => _; rewrite ?andbF ?andbT.
    subst B.
    have P (a b: bool) : a ↔ b → a = b :> bool.
    + case: a b => - [] //; last by intuition.
      by case => /(_ erefl).
    apply: P.
    rewrite !zify first_frameE !wunsigned_top_stack.
    change (stk_root (free_stack m)) with (stk_root m).
    Psatz.lia.
  Qed.

  Lemma fss_read_old m p s :
    valid_pointer (free_stack m) p s →
    read_mem m p s = read_mem (free_stack m) p s.
  Proof.
    move => /dup[] ok_p_s' /valid_pointerP[] al_p valid_p.
    have ok_p_s : valid_pointer m p s.
    + apply/valid_pointerP; apply: (conj al_p) => k /valid_p.
      by rewrite (fss_valid m) => /andP[].
    by rewrite /read_mem /CoreMem.read /= /validr /validrb ok_p_s ok_p_s'.
  Qed.

  Lemma free_stackP m :
    free_stack_spec m (free_stack m).
  Proof.
    split => *.
    - exact: fss_read_old.
    - rewrite !top_stackE; exact: fss_valid.
    - by [].
    - by [].
    rewrite /memory_model.frames /= /stack_frames /= /stack_blocks.
    case: (frames m) => //= f fr.
    by case: (stack_blocks_rec _ _).
  Qed.

  Lemma top_stack_after_aligned_alloc p ws sz :
    is_align p ws →
    top_stack_after_alloc p ws sz = (p + wrepr Uptr (- round_ws ws sz))%R.
  Proof.
    rewrite /top_stack_after_alloc /is_align /do_align /=.
  Admitted.

  Lemma alloc_stack_complete m ws sz sz' :
    let: old_size:= sub (stack_root m) (memory_model.top_stack m) in
    let: max_size := sub (stack_root m) (stack_limit m) in
    let: available := max_size - old_size in
    [&& 0 <=? sz, 0 <=? sz' &
    if is_align (memory_model.top_stack m) ws
    then round_ws ws (sz + sz') <=? available (* tight bound *)
    else sz + sz' + wsize_size ws <=? available (* loose bound, exact behavior is under-specified *)
    ] →
    ∃ m', alloc_stack m ws sz sz' = ok m'.
  Proof.
    rewrite !top_stackE !zify => - [ sz_pos ] [ sz'_pos ].
    rewrite /alloc_stack.
    rewrite /valid_frame /=.
    case: Sumbool.sumbool_of_bool; first by eauto.
    rewrite /footprint_of_frame /= -!subE.
    move => /negbT; rewrite !zify => X no_overflow; elim: X.
    refine ((λ x, conj (conj sz_pos (proj1 x)) (proj2 x)) _).
    have -> : footprint_of_stack (frames m) = sub (stk_root m) (top_stack m).
    - rewrite subE wunsigned_top_stack; ring.
    change (@align_word Uptr) with do_align.
    rewrite -/(top_stack_after_alloc (top_stack m) ws (sz + sz')).
    case: ifPn no_overflow => top_align; rewrite zify => no_overflow.
    { (* old top stack is aligned for ws *)
      rewrite top_stack_after_aligned_alloc //.
      have size_big := @round_ws_range ws (sz + sz').
      have size_small : 0 <= round_ws ws (sz + sz') <= wunsigned (top_stack m).
      - move: no_overflow; rewrite !subE.
        have := wunsigned_range (stk_limit m).
        Psatz.lia.
      rewrite sub_add_small_R // subxx.
      Psatz.lia. }
    (* old top stack is not aligned *)
    split.
    { rewrite -Z.le_add_le_sub_r /=.
      etransitivity; last by apply/sub_le; exact: (proj2 (align_word_range _ _)).
      rewrite sub_add_small_R; first by rewrite subxx; Psatz.lia.
      move: no_overflow; rewrite !subE.
      have := wunsigned_range (stk_limit m).
      have := wsize_size_pos ws.
      Psatz.lia. }
    ring_simplify.
    rewrite Z.le_add_le_sub_r.
    etransitivity; last exact: no_overflow.
    rewrite subE; apply: top_stack_after_alloc_bounded.
    move: no_overflow; rewrite !subE.
    have := wunsigned_range (stk_limit m).
    have := wsize_size_pos ws.
    Psatz.lia.
  Qed.

End MemoryI.
