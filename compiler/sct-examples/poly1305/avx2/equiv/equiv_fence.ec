require import Poly1305 Poly1305_safe_fence.
from Jasmin require import JModel.

equiv test : 
  Poly1305.M.poly1305_avx2 ~ Poly1305_safe_fence.M.poly1305_avx2_v4_safe_fence
  : ={Glob.mem, arg} ==> ={Glob.mem, res}.
proof.
  sim.
qed.

