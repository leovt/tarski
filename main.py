from proof import ProofContext
from tarski import axioms, Congruent, Equal, Between
from formula import (UniversalQuantifier as ForAll,
                     ExistentialQuantifier as Exists)

p = ProofContext(axioms)
x,y = p.start_context(2)
F1 = p.specialise(axioms[1], (y,x,x,y,x,y))
F2 = p.specialise(axioms[0], (y,x))
p.conjunction(F2, F2)
F3 = p.modus_ponens(F1)
Thm_2_1 = p.directproof(F3)
assert Thm_2_1 == ForAll((1,2), Congruent(1,2,1,2))

x,y,r,s = p.start_context(4)
F3 = p.assume(Congruent(x,y,r,s))
F4 = p.specialise(Thm_2_1, (x,y))
F5 = p.specialise(axioms[1], (x,y,r,s,x,y))
F6 = p.conjunction(F3, F4)
F7 = p.modus_ponens(F5)
Thm_2_2 = p.directproof(Congruent(r,s,x,y))
assert Thm_2_2 == ForAll((1,2,3,4), Congruent(1,2,3,4) > Congruent(3,4,1,2))

