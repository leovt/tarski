from proof import ProofContext
from tarski import axioms, Congruent, Equal, Between


p = ProofContext()
x,y = p.start_context(2)
F1 = p.specialise(axioms[1], (x,y,y,x,y,x))
F2 = p.specialise(axioms[0], (x,y))
p.conjunction(F2, F2)
F3 = p.modus_ponens(F1)
Thm1 = p.directproof(F3)

x,y,r,s = p.start_context(4)
F3 = p.assume(Congruent(x,y,r,s))
F4 = p.specialise(Thm1, (y,x))
F5 = p.specialise(axioms[1], (x,y,r,s,x,y))
F6 = p.conjunction(F3, F4)
F7 = p.modus_ponens(F5)
Thm2 = p.directproof(Congruent(r,s,x,y))
