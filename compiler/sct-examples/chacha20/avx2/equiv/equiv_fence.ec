require import Chacha20 Chacha20_safe_fence.
from Jasmin require import JModel.

equiv test:
   Chacha20.M.chacha20_avx2 ~ 
   Chacha20_safe_fence.M.chacha20_avx2_v4_safe_fence : 

   ={arg, Glob.mem} ==> 
   ={res, Glob.mem}.
proof.
  sim.
qed.
