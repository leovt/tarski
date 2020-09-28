from proof import ProofContext
from tarski import axioms, Congruent, Equal, Between, equality_axioms
from formula import (UniversalQuantifier as ForAll,
                     ExistentialQuantifier as Exists)

QED = '                                                      #'

def theorem(statement):
    def verifyer(proof):
        print(f'Theorem ({proof.__name__}):  {proof.__doc__.strip()}')
        print(f'  {statement}\nProof:')
        deduction = proof()
        assert deduction == statement
        print(QED)
        return deduction
    return verifyer

p = ProofContext(axioms+equality_axioms)

@theorem(ForAll((1,2), Equal(1,2) > Equal(2,1)))
def symmetry_equal():
    "Equality is symmetric"
    x,y = p.start_context(2)
    E1 = p.assume(Equal(x,y))
    E2 = p.specialise(equality_axioms[0], (x,))
    E3 = p.substitute_equal(E2, Equal(y,x), E1)
    return p.directproof(E3)

@theorem(ForAll((1,2), Congruent(1,2,1,2)))
def Thm_2_1():
    """segment congruence is symmetric."""
    x,y = p.start_context_names('xy')
    F2 = p.specialise(axioms[0], (y,x))
    P = p.conjunction(F2, F2)
    F1 = p.specialise(axioms[1], (y,x,x,y,x,y))
    F3 = p.modus_ponens2(P, Congruent(x,y,x,y))
    return p.directproof(F3)

@theorem(ForAll((1,2,3,4), Congruent(1,2,3,4) > Congruent(3,4,1,2)))
def Thm_2_2():
    """segment congruence is reflexive"""
    x,y,r,s = p.start_context_names('xyrs')
    F3 = p.assume(Congruent(x,y,r,s))
    F4 = p.specialise(Thm_2_1, (x,y))
    F5 = p.specialise(axioms[1], (x,y,r,s,x,y))
    F6 = p.conjunction(F3, F4)
    F7 = p.modus_ponens(F5)
    return p.directproof(Congruent(r,s,x,y))

@theorem(ForAll((1,2,3,4,5,6), Congruent(1,2,3,4) & Congruent(3,4,5,6) > Congruent(1,2,5,6)))
def Thm_2_3():
    """segment congruence is transitive"""
    a,b,c,d,e,f = p.start_context(6)
    H1 = p.assume(Congruent(a,b,c,d))
    H2 = p.assume(Congruent(c,d,e,f))
    H3 = p.specialise(Thm_2_2,(a,b,c,d))
    H4 = p.modus_ponens(H3)
    p.conjunction(H4,H2)
    H5 = p.specialise(axioms[1], (c,d,a,b,e,f))
    H6 = p.modus_ponens(H5)
    return p.directproof(H6)

@theorem(ForAll((1,2,3,4), Congruent(1,2,3,4)>Congruent(2,1,3,4)))
def Thm_2_4():
    """segement congruence is independent of orientation of the first segment"""
    a,b,c,d = p.start_context(4)
    X0 = p.assume(Congruent(a,b,c,d))
    X1 = p.specialise(axioms[0], (b,a))
    X2 = p.specialise(Thm_2_3, (b,a,a,b,c,d))
    p.conjunction(X1, X0)
    X3 = p.modus_ponens(X2)
    return p.directproof(X3)


@theorem(ForAll((1,2,3,4), Congruent(1,2,3,4) > Congruent(1,2,4,3)))
def Thm_2_5():
    """segement congruence is independent of orientation of the second segment"""
    a,b,c,d = p.start_context(4)
    X0 = p.assume(Congruent(a,b,c,d))
    X1 = p.specialise(Thm_2_2, (a,b,c,d))
    X2 = p.specialise(Thm_2_4, (c,d,a,b))
    X3 = p.specialise(Thm_2_2, (d,c,a,b))
    X4 = p.modus_ponens(X1)
    X5 = p.modus_ponens(X2)
    X6 = p.modus_ponens(X3)
    return p.directproof(X6)

@theorem(ForAll((1,2,3,4), Congruent(1,2,3,4) > Congruent(2,1,4,3)))
def Thm_2_5_bis():
    """segement congruence is independent of orientation of both segments"""
    a,b,c,d = p.start_context(4)
    X0 = p.assume(Congruent(a,b,c,d))
    X1 = p.modus_ponens(p.specialise(Thm_2_4, (a,b,c,d)))
    X2 = p.modus_ponens(p.specialise(Thm_2_5, (b,a,c,d)))
    return p.directproof(X2)

@theorem(ForAll((1,2), Congruent(1,1,2,2)))
def Thm_2_8():
    """all degenerate segments are congruent"""
    a,b = p.start_context(2)
    #str(a), str(b)
    X1 = p.specialise(axioms[3], (b,a,b,b))
    (c,), X2 = p.instantiate(X1)
    #str(c)
    X2b = p.deduce_right(X2)
    X3 = p.specialise(axioms[2], (a,c,b))
    X4 = p.modus_ponens(X3)
    X5 = p.substitute_equal(X2b, Congruent(a,a,b,b), X4)
    return p.directproof(X5)

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

a,b,c,a1,b1,c1 = p.start_context(6)
B1 = p.assume(Between(a,b,c) & Between(a1,b1,c1))
B2 = p.assume(Congruent(a,b,a1,b1))
B3 = p.assume(Congruent(b,c,b1,c1))
B4 = p.specialise(Thm_2_8, (a,a1))
B5 = p.modus_ponens(p.specialise(Thm_2_5_bis, (a,b,a1,b1)))
B6 = p.conjunction(p.conjunction(p.conjunction(p.conjunction(B1,B2),B3),B4),B5)
assert B6 == AFS(a,b,c,a,a1,b1,c1,a1)
p.start_context(0)
C1 = p.assume(Equal(a,b))
C2 = p.substitute_equal(B2, Congruent(a,a,a1,b1), C1)
C3 = p.modus_ponens(p.specialise(Thm_2_2, (a,a,a1,b1)))
C4 = p.modus_ponens(p.specialise(axioms[2], (a1,b1,a)))
C5 = p.substitute_equal(B3, Congruent(a,c,b1,c1), C1)
C6 = p.substitute_equal(C5, Congruent(a,c,a1,c1), C4)
assert C6 == Congruent(a,c,a1,c1)
B7 = p.directproof(C6)
p.start_context(0)
D1 = p.assume(-Equal(a,b))
D2 = p.conjunction(D1, B6)
D3 = p.modus_ponens(p.specialise(axioms[4], (a,b,c,a,a1,b1,c1,a1)))
D4 = p.modus_ponens(p.specialise(Thm_2_5_bis, (c,a,c1,a1)))
assert D4 == Congruent(a,c,a1,c1)
B8 = p.directproof(D4)
p.tertium_non_datur(Equal(a,b))
B9 = p.disjunction_elimination(Equal(a,b), -Equal(a,b), Congruent(a,c,a1,c1))
Thm_2_11 = p.directproof(B9)
assert Thm_2_11 == ForAll((1,2,3,4,5,6),
                          Between(1,2,3) & Between(4,5,6) &
                          Congruent(1,2,4,5) & Congruent(2,3,5,6)
                          > Congruent(1,3,4,6))

a,b = p.start_context(2)
A1 = p.specialise(axioms[3], (a,b,b,b))
(x,),A2 = p.instantiate(A1)
A3 = p.deduce_left(A2)
A4 = p.deduce_right(A2)
A5 = p.modus_ponens(p.specialise(axioms[2], (b,x,b)))
A6 = p.substitute_equal(A3, Between(a,b,b), A5)
Thm_3_1 = p.directproof(A6)
assert Thm_3_1 == ForAll((1,2), Between(1,2,2))

a,b,c = p.start_context(3)
p.conjunction(
    p.assume(Between(a,b,c)),
    p.specialise(Thm_3_1, (b,c)))
A1=p.modus_ponens(p.specialise(axioms[6], (a,b,b,c,c)))
(x,),A2=p.instantiate(A1)
p.deduce_left(A2)
A3 = p.modus_ponens(p.specialise(axioms[5], (b,x)))
A4 = p.substitute_equal(p.deduce_right(A2), Between(c,b,a), A3)
Thm_3_2 = p.directproof(A4)
assert Thm_3_2 == ForAll((1,2,3), Between(1,2,3) > Between(3,2,1))

a,b = p.start_context_names('ab')
p.specialise(Thm_3_1, (b,a))
p.specialise(Thm_3_2, (b,a,a))
p.modus_ponens2(Between(b,a,a), Between(a,a,b))
Thm_3_3 = p.directproof(Between(a,a,b))
assert Thm_3_3 == ForAll((1,2), Between(1,1,2))
