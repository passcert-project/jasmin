require import Chacha20 Chacha20_safe_movcc.
from Jasmin require import JModel.

equiv test:
   Chacha20.M.chacha20_avx2 ~ 
   Chacha20_safe_movcc.M.chacha20_avx2_v4_safe_movcc : 

   ={arg, Glob.mem} ==> 
   ={res, Glob.mem}.
proof.
  proc.
  if => //.
  + by sim.
  wp.
  call (_: ={Glob.mem}); last by auto.
  seq 4 7 : (={Glob.mem, output, plain, len, key, nonce, counter, k, st, s_r16, s_r8} /\ 
             r512{2} = (W64.of_int 512) /\
             s_plain{2} = plain{2} /\ s_output{2} = output{2}).
  + by wp; sim />.
  seq 1 1 : (={Glob.mem, st, k, s_r16, s_r8, output,plain,len}); last by sim.
  unroll {1} 1.
  if => //; last by rcondf{1} ^while; auto.
  while (={Glob.mem, st, k, s_r16, s_r8, output,plain,len}).
  + sim; auto; smt ( W32.ultE W32.uleE).
  sim; auto; smt ( W32.ultE W32.uleE).
qed.
