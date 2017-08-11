from proof import ProofContext
from tarski import axioms, Congruent, Equal, Between, equality_axioms
from formula import (UniversalQuantifier as ForAll,
                     ExistentialQuantifier as Exists)

p = ProofContext(axioms+equality_axioms)
x,y = p.start_context(2)
E1 = p.assume(Equal(x,y))
E2 = p.specialise(equality_axioms[0], (x,))
E3 = p.substitute_equal(E2, Equal(y,x), E1)
symmetry_equal = p.directproof(E3)
assert symmetry_equal == ForAll((1,2), Equal(1,2) > Equal(2,1))

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

a,b,c,d,e,f = p.start_context(6)
H1 = p.assume(Congruent(a,b,c,d))
H2 = p.assume(Congruent(c,d,e,f))
H3 = p.specialise(Thm_2_2,(a,b,c,d))
H4 = p.modus_ponens(H3)
p.conjunction(H4,H2)
H5 = p.specialise(axioms[1], (c,d,a,b,e,f))
H6 = p.modus_ponens(H5)
Thm_2_3 = p.directproof(H6)
assert Thm_2_3 == ForAll((1,2,3,4,5,6), Congruent(1,2,3,4) & Congruent(3,4,5,6) > Congruent(1,2,5,6))

a,b,c,d = p.start_context(4)
X0 = p.assume(Congruent(a,b,c,d))
X1 = p.specialise(axioms[0], (b,a))
X2 = p.specialise(Thm_2_3, (b,a,a,b,c,d))
p.conjunction(X1, X0)
X3 = p.modus_ponens(X2)
Thm_2_4 = p.directproof(X3)
assert Thm_2_4 == ForAll((1,2,3,4), Congruent(1,2,3,4)>Congruent(2,1,3,4))

import formula
formula.symbol_map[:] = [formula.SymbolMap() for _ in formula.symbol_map]

a,b,c,d = p.start_context(4)
X0 = p.assume(Congruent(a,b,c,d))
X1 = p.specialise(Thm_2_2, (a,b,c,d))
X2 = p.specialise(Thm_2_4, (c,d,a,b))
X3 = p.specialise(Thm_2_2, (d,c,a,b))
X4 = p.modus_ponens(X1)
X5 = p.modus_ponens(X2)
X6 = p.modus_ponens(X3)
Thm_2_5 = p.directproof(X6)
assert Thm_2_5 == ForAll((1,2,3,4), Congruent(1,2,3,4) > Congruent(1,2,4,3))

formula.symbol_map[:] = [formula.SymbolMap() for _ in formula.symbol_map]
a,b = p.start_context(2)
str(a), str(b)
X1 = p.specialise(axioms[3], (b,a,b,b))
(c,), X2 = p.instantiate(X1)
str(c)
X2b = p.deduce_right(X2)
X3 = p.specialise(axioms[2], (a,c,b))
X4 = p.modus_ponens(X3)
X5 = p.substitute_equal(X2b, Congruent(a,a,b,b), X4)
Thm_2_8 = p.directproof(X5)
assert Thm_2_8 == ForAll((1,2), Congruent(1,1,2,2))

def AFS(a,b,c,d,a1,b1,c1,d1):
    '''Definition 2.10: part of the condition for axiom 5'''
    return (Between(a,b,c) & Between(a1,b1,c1)
            & Congruent(a,b,a1,b1)
            & Congruent(b,c,b1,c1)
            & Congruent(a,d,a1,d1)
            & Congruent(b,d,b1,d1))

assert axioms[4] == ForAll((11,12,13,14,21,22,23,24), 
                           -Equal(11,12) & 
                           AFS(11,12,13,14,21,22,23,24) 
                           > Congruent(13,14,23,24))
