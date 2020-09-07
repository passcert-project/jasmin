require import AllCore IntDiv.
require import Poly1305 Poly1305_last Poly1305_safe_movcc_last.
from Jasmin require import JWord JModel.
require import Array2 Array3 Array4 Array5.
require import WArray16 WArray24 WArray64 WArray96 WArray128 WArray160.

(*equiv eq_last : 
  Poly1305_last.M.poly1305_ref3_last ~ M.poly1305_ref3_last : ={Glob.mem, arg} ==> ={Glob.mem, res}.
proof. by sim. qed.
*)

equiv eq_ref3_update :   
  Poly1305_last.M.poly1305_ref3_update ~ M.poly1305_ref3_update : 
   ={Glob.mem, in_0, inlen, h, r} ==> ={Glob.mem, res}.
proof.
  proc.
  unroll{1}1.
  sp 0 1; if; 1: done.
  + while (={Glob.mem, in_0, inlen, h, r}).
    + by sim; auto; smt (W64.uleE W64.ultE).
    conseq (_: ={Glob.mem, in_0, inlen, h, r}) => //.
    by sim; auto; smt (W64.uleE W64.ultE).
  by rcondf{1} ^while; auto.
qed.

equiv eq_update : 
  Poly1305_last.M.poly1305_avx2_update ~
  M.poly1305_avx2_update : 
  ={Glob.mem, in_0, len, r4444, r4444x5, r1234, r1234x5} ==> ={Glob.mem, res}.
proof.
  proc.
  sim.
  while (={Glob.mem, in_0, len, h, m, in_0, r4444, r4444x5, r1234, r1234x5, s_mask26, s_bit25}).
  + by sim; auto; smt (W64.uleE W64.ultE).
  conseq (_: ={Glob.mem, in_0, len, h, m, in_0, r4444, r4444x5, r1234, r1234x5, s_mask26, s_bit25}) => />.
  by sim.
qed.

equiv test1 : 
  Poly1305_last.M.poly1305_avx2 ~ Poly1305_safe_movcc_last.M.poly1305_avx2_v4_safe_movcc_last
  : ={Glob.mem, arg} ==> ={Glob.mem, res}.
proof.
  proc; wp.
  if => //.
  + call (_: ={Glob.mem}); last by auto.
    sim; call eq_ref3_update.
    conseq (_: ={Glob.mem, in_0, len, h, r, k}) => />.
    by sim.
  call (_: ={Glob.mem}); last by auto.
  sim.
  call eq_ref3_update.
  conseq (_: ={Glob.mem, in_0, len, h, r, k}) => />.
  call eq_update.
  conseq (: ={Glob.mem, in_0, len, r, k, r4444, r4444x5, r1234, r1234x5}) => />.
  by sim.
qed.

module Aux = {
  var ji : int

  proc load_last_add (in_0:W64.t, len:int, s:W64.t Array2.t) : int * W64.t Array2.t  = {
    var aux: bool;
    var aux_0: W64.t;
    var c: W8.t;
    var j: int;
 
    j <- 0;
    while ((j < len)) {
      c <- loadW8 Glob.mem (W64.to_uint in_0 + j);
      s <-
      Array2.init
      (WArray16.get64 (WArray16.set8 (WArray16.init64 (fun i => s.[i])) j c));
      j <- j + 1;
    }
    return (j, s);
  }

(*  proc load_last_add_if (in_0:W64.t, len': int, len: int, s:W64.t Array2.t, j : int) : int * W64.t Array2.t  = {
    var aux: bool;
    var aux_0: W64.t;
    var c:W8.t;

    if (j <= len - len') (j, s) <@ load_last_add(in_0, j + len', s, j);
    (j,s) <@ load_last_add(in_0, len, s, j);
    return (j,s);
  }*)

  proc load_last_add_ifs (in_0:W64.t, len:int, s:W64.t Array2.t) :
     int * W64.t Array2.t  = {
    var c64:W64.t;
    var c32:W32.t;
    var c16:W16.t;
    var c8:W8.t;
    var j:int;

    j <- 0;
    if (8 <= len) {
      c64 <- loadW64 Glob.mem (W64.to_uint in_0 + j);
      s.[j] <- c64;
      len <- len - 8;
      j <- j + 1; 
    }
    j <- j * 2; 
    if (4 <= len) {
      c32 <- loadW32 Glob.mem (W64.to_uint in_0 + 4 * j);
      s <-
      Array2.init
      (WArray16.get64 (WArray16.set32 (WArray16.init64 (fun i => s.[i])) j c32));
      len <- len - 4;
      j <- j + 1;
    } 
    j <- j * 2; 
    if (2 <= len) {
      c16 <- loadW16 Glob.mem (W64.to_uint in_0 + 2 * j);
      s <-
      Array2.init
      (WArray16.get64 (WArray16.set16 (WArray16.init64 (fun i => s.[i])) j c16));
      len <- len - 2;
      j <- j + 1;
    }
    j <- j * 2; 
    if (1 <= len) {
      c8 <- loadW8 Glob.mem (W64.to_uint in_0 + j);
      s <-
      Array2.init
      (WArray16.get64 (WArray16.set8 (WArray16.init64 (fun i => s.[i])) j c8));
      j <- j + 1;
    }
    return (j, s);
  }
}.

phoare Aux_load_last_add mem0 in0 len0 s0 : [Aux.load_last_add :
   Glob.mem = mem0 /\ in_0 = in0 /\ len = len0 /\ s = s0 /\ 0 <= len < 16 ==> 
   let (j,s) = res in
   j = len0 /\
   forall k, 0 <= k < 16 =>
     s.[k %/ 8] \bits8 (k %% 8) = 
      if 0 <= k < len0 then loadW8 mem0 (W64.to_uint in0 + k)
      else s0.[k %/ 8] \bits8 (k %% 8)] = 1%r.
proof.
  proc.
  while
    (0 <= j <= len /\ len < 16 /\
     forall k, 0 <= k < 16 =>
     s.[k %/ 8] \bits8 (k %% 8) = 
      if 0 <= k < j then loadW8 Glob.mem (W64.to_uint in_0 + k)
      else s0.[k %/ 8] \bits8 (k %% 8)) (len - j).
  + move=> z; auto => /> &m h0j _ hl hs hjl'; split; 2:smt().
    split; 1:smt().
    move=> k h0k hk.
    rewrite Array2.initiE 1:/# WArray16.get64E W8u8.pack8bE 1:/#.
    rewrite W8u8.Pack.initiE 1:/# /=  WArray16.get_set8E 1:/#. 
    have -> : 8 * (k %/ 8) + k %% 8 = k by smt().
    case: (k = j{m}) => [->> /#| ?].
    have -> : (k < j{m} + 1) = (0 <= k < j{m}) by smt().
    by rewrite -(hs k _) 1:// /WArray16.init64 WArray16.initiE.
  auto => /> /#.
qed.

phoare Aux_load_last_add_ifs mem0 in0 len0 s0 : [ Aux.load_last_add_ifs :
  Glob.mem = mem0 /\ in_0 = in0 /\ len = len0 /\ s = s0 /\ 0 <= len < 16 ==> 
   let (j,s) = res in
   j = len0 /\
   forall k, 0 <= k < 16 =>
     s.[k %/ 8] \bits8 (k %% 8) = 
      if 0 <= k < len0 then loadW8 mem0 (W64.to_uint in0 + k)
      else s0.[k %/ 8] \bits8 (k %% 8)] = 1%r.
proof.
  proc.
  conseq (_: true ==> true) (_: Glob.mem = mem0 /\ in_0 = in0 /\ len = len0 /\ s = s0 /\ 0 <= len < 16 ==>
    (j = len0 /\
     forall (k : int),
       0 <= k < 16 =>
       (s.[k %/ 8] \bits8 k %% 8) = if 0 <= k < len0 then loadW8 mem0 (to_uint in0 + k) else s0.[k %/ 8] \bits8 k %% 8)) => //;
     last by auto.
  seq 3 : ( Glob.mem = mem0 /\ in_0 = in0 /\ 0 <= len0 < 16 /\ 0 <= j <= 2 /\ 0 <= len < 8 /\
            len = len0 - 4 * j /\ 
           forall k, 0 <= k < 16 =>
             s.[k %/ 8] \bits8 (k %% 8) = 
             if 0 <= k < 4 * j then loadW8 mem0 (W64.to_uint in0 + k)
             else s0.[k %/ 8] \bits8 (k %% 8)).
  + auto => /> &m ??; split => ?; split; 1,3,4:smt ().
    move=> k ??.
    case: (k < 8) => hk.
    + rewrite divz_small 1:// modz_small 1:// Array2.get_setE 1:// /=.
      by rewrite W8u8.pack8bE 1:// W8u8.Pack.initiE.
    have -> : (k %/8 = 1) by smt().
    by rewrite Array2.get_setE.
  seq 2 : ( Glob.mem = mem0 /\ in_0 = in0 /\ 0 <= len0 < 16 /\ 0 <= j <= 6 /\ 0 <= len < 4 /\
            len = len0 - 2 * j /\ 
           forall k, 0 <= k < 16 =>
             s.[k %/ 8] \bits8 (k %% 8) = 
             if 0 <= k < 2 * j then loadW8 mem0 (W64.to_uint in0 + k)
             else s0.[k %/ 8] \bits8 (k %% 8)).
  + auto => /> &m ?????? heq; split => *; split; 1,3,4:smt ().
    split; 1: smt().
    split; 1: smt().
    move=> k ??.
    rewrite Array2.initiE 1:/# WArray16.get64E W8u8.pack8bE 1:/# W8u8.Pack.initiE 1:/# /=.
    have -> : 8 * (k %/ 8) + k %% 8 = k by smt().  
    rewrite WArray16.set32E WArray16.initiE 1:/# /=.
    case: (4 * j{m} <= k < 4 * (j{m} + 1)) => ?.
    + have -> /= : k < 2 * ((j{m} + 1) * 2) by smt().
      by rewrite /loadW32 W4u8.pack4bE 1:/# W4u8.Pack.initiE /#.
    have := heq k _; 1:done.
    have -> -> /#: s{m}.[k %/ 8] \bits8 k %% 8 = (WArray16.init64 ("_.[_]" s{m})).[k].
    by rewrite /WArray16.init64 WArray16.initiE.
  seq 2 : ( Glob.mem = mem0 /\ in_0 = in0 /\ 0 <= len0 < 16 /\ 0 <= j <= 14 /\ 0 <= len < 2 /\
            len = len0 - j /\ 
           forall k, 0 <= k < 16 =>
             s.[k %/ 8] \bits8 (k %% 8) = 
             if 0 <= k < j then loadW8 mem0 (W64.to_uint in0 + k)
             else s0.[k %/ 8] \bits8 (k %% 8)).
  + auto => /> &m ?????? heq; split => *; split; 1,3,4:smt ().
    split; 1: smt().
    split; 1: smt().
    move=> k ??.
    rewrite Array2.initiE 1:/# WArray16.get64E W8u8.pack8bE 1:/# W8u8.Pack.initiE 1:/# /=.
    have -> : 8 * (k %/ 8) + k %% 8 = k by smt().  
    rewrite WArray16.set16E WArray16.initiE 1:/# /=.
    case: (2 * j{m} <= k < 2 * (j{m} + 1)) => ?.
    + have -> /= : k < (j{m} + 1) * 2 by smt().
      by rewrite /loadW16 W2u8.pack2bE 1:/# W2u8.Pack.initiE /#.
    have := heq k _; 1:done.
    have -> -> /#: s{m}.[k %/ 8] \bits8 k %% 8 = (WArray16.init64 ("_.[_]" s{m})).[k].
    by rewrite /WArray16.init64 WArray16.initiE.
  auto => /> &m ?????? heq; split => *; split; 1,3,4:smt ().
  move=> k ??.
  rewrite Array2.initiE 1:/# WArray16.get64E W8u8.pack8bE 1:/# W8u8.Pack.initiE 1:/# /=.
  have -> : 8 * (k %/ 8) + k %% 8 = k by smt().  
  rewrite /WArray16.set8 WArray16.get_setE 1:/#.
  case: (k = j{m}) => [->> /#| ?].  
  have := heq k _; 1:done.
  have -> -> /#: s{m}.[k %/ 8] \bits8 k %% 8 = (WArray16.init64 ("_.[_]" s{m})).[k].
  by rewrite /WArray16.init64 WArray16.initiE.
qed.
  
equiv eq_load_last_add : 
  Poly1305.M.load_last_add ~ Poly1305_last.M.load_last_add : 
  ={arg, Glob.mem} /\ to_uint len{1} < 16 /\
  (to_uint in_0 + to_uint len){1} <= W64.modulus
  ==> ={res, Glob.mem}.
proof.
  proc; sim.
  seq 4 4 : (={h,in_0,len, Glob.mem, s, j} /\ to_uint j{1} = 0 /\
             to_uint len{1} < 16 /\  (to_uint in_0 + to_uint len){1} <= W64.modulus).
  + by auto.
  conseq />.
  transitivity{1}
    { (Aux.ji, s) <@ Aux.load_last_add(in_0, to_uint len, s);
      j <- W64.of_int Aux.ji;
    } 
    (={Glob.mem, h, in_0, len, s, j} /\  to_uint j{1} = 0 /\ to_uint len{1} < 16 
      /\ (to_uint in_0 + to_uint len){1} <= W64.modulus ==> ={j,s})
    (={Glob.mem, h, in_0, len, s, j} /\  to_uint j{1} = 0 /\ to_uint len{1} < 16 
      /\ (to_uint in_0 + to_uint len){1} <= W64.modulus ==> ={j,s});
      [ smt() | done | | ].
  + inline *; wp.
    while (={Glob.mem} /\ in_0{1} = in_00{2} /\ len0{2} = to_uint len{1} /\
             to_uint len{1} < 16 /\ j0{2} = to_uint j{1} /\ s{1} = s0{2} /\
             (to_uint in_0 + to_uint len){1} <= W64.modulus).
    + auto => /> &1 &2; rewrite !W64.ultE => *.
      rewrite to_uintD_small //= 1:/#.
      by rewrite W64.to_uintD_small 1:/#.
    auto => />; smt (W64.ultE W64.to_uint_cmp).
  transitivity{1} {
     (Aux.ji, s) <@ Aux.load_last_add_ifs(in_0, to_uint len, s);
     j <- W64.of_int Aux.ji; 
  }
  (={Glob.mem, h, in_0, len, s, j} /\  to_uint j{1} = 0 /\ to_uint len{1} < 16
    /\ (to_uint in_0 + to_uint len){1} <= W64.modulus ==> ={j,s})
  (={Glob.mem, h, in_0, len, s, j} /\  to_uint j{1} = 0 /\ to_uint len{1} < 16
    /\ (to_uint in_0 + to_uint len){1} <= W64.modulus ==> ={j,s});
   [ smt() | done | | ]; first last.
  + inline *.
    seq 6 2 : (={Glob.mem} /\ s0{1} = s{2} /\ j0{1} = to_uint j{2} /\
               in_00{1} = in_0{2} /\ len0{1} = to_uint len{2} /\
               j0{1} <= 2 /\ (to_uint in_00 + 4 * j0 + len0){1} <= W64.modulus ).
    + auto => /> &2 h1 h2 h3.
      rewrite !(W64.uleE) /= h1 => />.
      have ->: j{2} = W64.of_int 0 by rewrite -(W64.to_uintK j{2}) h1.
      rewrite /= !W64.shl_shlw 1,2:// !W64.to_uint_shl //= => *.
      rewrite W64.to_uintB 1:W64.uleE //= /#.
    seq 2 2 : (={Glob.mem} /\ s0{1} = s{2} /\ j0{1} = to_uint j{2} /\
               in_00{1} = in_0{2} /\ len0{1} = to_uint len{2} /\
               j0{1} <= 6 /\ (to_uint in_00 + 2 * j0 + len0){1} <= W64.modulus).
    + auto => /> &2.
      rewrite !(W64.uleE) /= => />.
      rewrite /= !W64.shl_shlw 1,2:// !W64.to_uint_shl //= => *.
      have ? := W64.to_uint_cmp j{2}.
      have h4j : to_uint (W64.of_int 4 * j{2}) = 4 * W64.to_uint j{2}.
      + by rewrite W64.to_uintM_small /= /#.
      rewrite (W64.to_uintD_small j{2}) /= 1:/# !IntDiv.modz_small /= 1,2:/#. 
      split; 2: smt().
      move=> *; rewrite W64.to_uintB 1:W64.uleE //=.
      rewrite W64.to_uintD_small h4j /#.

    seq 2 2 : (={Glob.mem} /\ s0{1} = s{2} /\ j0{1} = to_uint j{2} /\
               in_00{1} = in_0{2} /\ len0{1} = to_uint len{2} /\
               j0{1} <= 14 /\ (to_uint in_00 + j0 + len0){1} <= W64.modulus).
    + auto => /> &2.
      rewrite !(W64.uleE) /= => />.
      rewrite /= !W64.shl_shlw 1,2:// !W64.to_uint_shl //= => *.
      have ? := W64.to_uint_cmp j{2}.
      have h4j : to_uint (W64.of_int 2 * j{2}) = 2 * W64.to_uint j{2}.
      + by rewrite W64.to_uintM_small /= /#.
      rewrite (W64.to_uintD_small j{2}) /= 1:/# !IntDiv.modz_small /= 1,2:/#. 
      split; 2: smt().
      move=> *; rewrite W64.to_uintB 1:W64.uleE //=.
      rewrite W64.to_uintD_small h4j /#.
    seq 1 1 : (={Glob.mem} /\ s0{1} = s{2} /\ j0{1} = to_uint j{2} /\
               in_00{1} = in_0{2} /\ len0{1} = to_uint len{2} /\
               j0{1} <= 15).
    + auto => /> &2.
      rewrite !(W64.uleE) /= => /> *.
      have ? := W64.to_uint_cmp j{2}.
      rewrite (W64.to_uintD_small j{2}) /= 1:/#.
      split; 2: smt().
      by move=> *; rewrite W64.to_uintD_small /= /#.
    by auto.
  wp.
  ecall{1} (Aux_load_last_add Glob.mem{1} in_0{1} (to_uint len{1}) s{1}).
  ecall{2} (Aux_load_last_add_ifs Glob.mem{1} in_0{1} (to_uint len{1}) s{1}).
  auto => /> &2 *; split; 1: smt (W64.to_uint_cmp).
  move=> ? [j1 s1] /= /> h1 [j2 s2] /= /> h2.
  apply Array2.tP => i hi.
  apply W8u8.wordP => j hj.
  pose k := 8 * i + j.
  have hk : 0 <= k < 16 by smt().
  have [-> ->] : i = k %/ 8 /\ j = k %% 8 by smt().
  by rewrite (h1 k hk) (h2 k hk).
qed.

equiv eq_last : 
  Poly1305.M.poly1305_ref3_last ~ Poly1305_last.M.poly1305_ref3_last : 
  ={Glob.mem, arg} /\ to_uint inlen{1} < 16 /\ (to_uint in_0 + to_uint inlen){1} <= W64.modulus ==> ={Glob.mem, res}.
proof. 
  proc. sim; sp 2 2.
  if => />; last by auto.
  sim; call eq_load_last_add; auto.
qed.

equiv last_eq_ref3_update :
  Poly1305.M.poly1305_ref3_update ~ Poly1305_last.M.poly1305_ref3_update : 
   ={Glob.mem, arg} /\ (to_uint in_0 + to_uint inlen){1} < W64.modulus ==> 
   ={Glob.mem, res} /\ to_uint res{1}.`2 < 16 /\
        (to_uint res{1}.`1 + to_uint res{1}.`2) < W64.modulus.
proof.
  proc => /=.
  while (={Glob.mem, h, r, in_0, inlen} /\ (to_uint in_0 + to_uint inlen){1} < W64.modulus).
  + wp. conseq (: ={h}); last by sim.
    move => />; rewrite W64.uleE /= => * .
    rewrite W64.to_uintD_small /= 1:/#. 
    by rewrite W64.to_uintB 1:W64.uleE //= /#.
  auto => /> &2 ??? ; rewrite W64.uleE /= /#.
qed.

equiv test2 : 
  Poly1305.M.poly1305_avx2 ~ Poly1305_last.M.poly1305_avx2
  : ={Glob.mem, arg} /\ (to_uint in_0 + to_uint inlen){1} < W64.modulus ==> ={Glob.mem, res}.
proof.
  proc.
  if => //.
  + call (_: ={Glob.mem, arg} /\ (to_uint in_0 + to_uint inlen){1} < W64.modulus ==> ={Glob.mem, res}); last by auto.
    proc.
    call eq_last.
    call last_eq_ref3_update; wp.
    conseq (: ={Glob.mem, out, in_0, k, h, r}) => />; 1: smt().
    by sim. 
  call (_: ={Glob.mem, arg} /\ 257 <= to_uint inlen{1} /\ (to_uint in_0 + to_uint inlen){1} < W64.modulus ==> ={Glob.mem, res}); last first.
  + by auto => />; rewrite W64.ultE; smt().
  proc.
  call eq_last.
  call last_eq_ref3_update.
  call (_ :  ={Glob.mem, arg} /\  257 <= to_uint len{1} /\ (to_uint in_0 + to_uint len){1} < W64.modulus ==> 
             ={Glob.mem, res} /\ (to_uint res{1}.`1 + to_uint res{1}.`2) < W64.modulus).
  + proc => /=.
    seq 10 10 : (#pre /\ ={h,h64,m,i, s_mask26, mask26, s_bit25}).
    + by conseq (: ={h,h64,m,i, s_mask26, mask26, s_bit25}) => />; sim.
    seq 1 1 :  (={Glob.mem, in_0, len, r4444, r4444x5, r1234, r1234x5, h, h64, m, i, s_mask26, mask26, s_bit25} /\
                 257 <= to_uint len{1} /\ to_uint in_0{1} - 64 + to_uint len{1} < 18446744073709551616).
    + inline *; auto => /> *.
      by rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp). 
    seq 2 2 : (={Glob.mem, in_0, len, r4444, r4444x5, r1234, r1234x5, h, h64, m, i, s_mask26, mask26, s_bit25} /\
                 to_uint in_0{1} + to_uint len{1} < 18446744073709551616).
    + wp; while (={Glob.mem, in_0, len, r4444, r4444x5, r1234, r1234x5, h, h64, m, i, s_mask26, mask26, s_bit25} /\ 64 <= to_uint len{1} /\
                 to_uint in_0{1} - 64 + to_uint len{1} < 18446744073709551616).
      + inline *; auto => />.
        move=> &2; rewrite W64.uleE /= => *.
        rewrite (W64.to_uintD_small in_0{2})/=; 1: smt(W64.to_uint_cmp).
        by rewrite W64.to_uintB 1:W64.uleE /= /#.
      auto => /> &2 ??; split; 1:smt(). 
      move=> ??; rewrite W64.uleE /= => *.
      by rewrite W64.to_uintB 1:W64.uleE //= /#.
    by conseq (: ={h, h64}) => />; sim.
  sp; conseq (: ={k, h, r, r4444, r4444x5, r1234, r1234x5}) => />;1: smt().
  by sim.
qed.

equiv test3 : 
  Poly1305.M.poly1305_avx2 ~ Poly1305_safe_movcc_last.M.poly1305_avx2_v4_safe_movcc_last : 
  ={Glob.mem, arg} /\ (to_uint in_0 + to_uint inlen){1} < W64.modulus ==> ={Glob.mem, res}.
proof.
  transitivity Poly1305_last.M.poly1305_avx2
     (={Glob.mem, arg} /\ (to_uint in_0 + to_uint inlen){1} < W64.modulus ==> ={Glob.mem, res})
     (={Glob.mem, arg} ==> ={Glob.mem, res} ) => />; 1: smt().
  + by apply test2. 
  by apply test1.
qed.

  


