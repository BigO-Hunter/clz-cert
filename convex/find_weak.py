import gen_cert as g, time, sys
from fractions import Fraction as F
sys.setrecursionlimit(1000000)
target = F(2213813, 10**10)
worst = [None]  # (bound, box)
def rec(u0,u1,v0,v1,d):
    b = g.box_bound(u0,u1,v0,v1)
    if b >= target or d >= 48 or (u1-u0) < g.RES_FLOOR or (v1-v0) < g.RES_FLOOR:
        if worst[0] is None or b < worst[0][0]:
            worst[0] = (b,(u0,u1,v0,v1))
            print(f"new worst: {float(b)*1e6:.3f}e-6 at u=[{float(u0):.6f},{float(u1):.6f}] v=[{float(v0):.6f},{float(v1):.6f}] d={d}", flush=True)
        return
    if u1-u0 >= v1-v0:
        m=(u0+u1)/2; rec(u0,m,v0,v1,d+1); rec(m,u1,v0,v1,d+1)
    else:
        m=(v0+v1)/2; rec(u0,u1,v0,m,d+1); rec(u0,u1,m,v1,d+1)
step = F(4,16)
for i in range(16):
    for j in range(16):
        u0,u1,v0,v1 = i*step,(i+1)*step,j*step,(j+1)*step
        if u0+v0 >= 4: continue
        rec(u0,u1,v0,v1,0)
print("DONE worst:", float(worst[0][0])*1e6, "e-6 at", [float(x) for x in worst[0][1]], flush=True)
