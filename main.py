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

@theorem(ForAll((1,2), -Equal(1,2) > -Equal(2,1)))
def symmetry_inequal():
    "Inquality is symmetric"
    x,y = p.start_context(2)
    p.assume(-Equal(x,y))
    p.specialise(symmetry_equal, (y,x))
    p.modus_tollens(Equal(y,x), Equal(x,y))
    return p.directproof(-Equal(y,x))

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

def show_congruent(p, a,b,c,d, try_reverse=True):
    if Congruent(a,b,c,d) in p.facts:
        return Congruent(a,b,c,d)
    if a==c and b==d:
        return p.modus_ponens(p.specialise(Thm_2_1, (a,b)))
    if Congruent(b,a,c,d) in p.facts:
        return p.modus_ponens(p.specialise(Thm_2_4, (b,a,c,d)))
    if Congruent(a,b,d,c) in p.facts:
        return p.modus_ponens(p.specialise(Thm_2_5, (a,b,d,c)))
    if Congruent(b,a,d,c) in p.facts:
        return p.modus_ponens(p.specialise(Thm_2_5_bis, (b,a,d,c)))
    if try_reverse:
        if show_congruent(p, c,d,a,b, False):
            return p.modus_ponens(p.specialise(Thm_2_2, (c,d,a,b)))

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

@theorem(ForAll((1,2,3,4,5,6),
         Between(1,2,3) & Between(4,5,6) &
         Congruent(1,2,4,5) & Congruent(2,3,5,6)
         > Congruent(1,3,4,6)))
def Thm_2_11():
    """adding line segments

    1--2===3   4--5===6    =>   1~~3  ==  4~~6
    """
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
    return p.directproof(B9)

@theorem(ForAll((1,2,3,4,5,6),
    -Equal(1,2) &
    Between(1,2,5) & Congruent(2,5,3,4) &
    Between(1,2,6) & Congruent(2,6,3,4) > Equal(5,6)))
def Thm_2_12():
    """uniqueness of adding line segments"""
    #ForAll((y,r,s,t), Exists((x,), Between(y,r,x) & Congruent(r,x,s,t)))
    q,a,b,c,x,y = p.start_context_names('qabcxy')
    A0 = p.assume(-Equal(q,a))
    A1x = p.assume(Between(q,a,x))
    A2x = p.assume(Congruent(a,x,b,c))
    A1y = p.assume(Between(q,a,y))
    A2y = p.assume(Congruent(a,y,b,c))
    Cqaqa = p.specialise(Thm_2_1, (q,a))
    p.conjunction(
        A2x,
        p.modus_ponens(p.specialise(Thm_2_2, (a,y,b,c))),
    )
    p.modus_ponens(p.specialise(Thm_2_3, (a,x,b,c,a,y)))
    p.conjunction(p.conjunction(p.conjunction(A1x, A1y), Cqaqa), Congruent(a,x,a,y))
    p.modus_ponens(p.specialise(Thm_2_11, (q,a,x,q,a,y)))
    print(axioms[4])
    p.conjunction(
        A0,
        p.conjunction(
        p.conjunction(
        p.conjunction(
            p.conjunction(
                p.conjunction(A1x, A1x),
                Cqaqa,
            ),
            p.specialise(Thm_2_1, (a,x))
            ),
            Congruent(q,x,q,y),
            ),
            Congruent(a,x,a,y))
        )
    p.modus_ponens(p.specialise(axioms[4], (q,a,x,x, q,a,x,y)))
    p.modus_ponens(p.specialise(Thm_2_2, (x,x,x,y)))
    p.modus_ponens(p.specialise(axioms[2], (x,y,x)))
    return p.directproof(Equal(x,y))

@theorem(ForAll((1,2), Between(1,2,2)))
def Thm_3_1():
    """right endpoint is between start and end"""
    a,b = p.start_context(2)
    A1 = p.specialise(axioms[3], (a,b,b,b))
    (x,),A2 = p.instantiate(A1)
    A3 = p.deduce_left(A2)
    A4 = p.deduce_right(A2)
    A5 = p.modus_ponens(p.specialise(axioms[2], (b,x,b)))
    A6 = p.substitute_equal(A3, Between(a,b,b), A5)
    return p.directproof(A6)

@theorem(ForAll((1,2,3), Between(1,2,3) > Between(3,2,1)))
def Thm_3_2():
    """between is symmetric in the endpoints"""
    a,b,c = p.start_context(3)
    p.conjunction(
        p.assume(Between(a,b,c)),
        p.specialise(Thm_3_1, (b,c)))
    A1=p.modus_ponens(p.specialise(axioms[6], (a,b,b,c,c)))
    (x,),A2=p.instantiate(A1)
    p.deduce_left(A2)
    A3 = p.modus_ponens(p.specialise(axioms[5], (b,x)))
    A4 = p.substitute_equal(p.deduce_right(A2), Between(c,b,a), A3)
    return p.directproof(A4)

@theorem(ForAll((1,2), Between(1,1,2)))
def Thm_3_3():
    """left endpoint is between start and end"""
    a,b = p.start_context_names('ab')
    p.specialise(Thm_3_1, (b,a))
    p.specialise(Thm_3_2, (b,a,a))
    p.modus_ponens2(Between(b,a,a), Between(a,a,b))
    return p.directproof(Between(a,a,b))
    assert Thm_3_3 == ForAll((1,2), Between(1,1,2))


@theorem(ForAll((1,2,3), Between(1,2,3) & Between(2,1,3) > Equal(1,2)))
def Thm_3_4():
    """squeeze point

    1-2----3  &&  2-1----3  ==>  1=2
    """
    a,b,c = p.start_context_names('abc')
    p.assume(Between(a,b,c) & Between(b,a,c))
    A7 = p.specialise(axioms[6], (a,b,b,a,c))
    Ex = p.modus_ponens(A7)
    (x,), Px = p.instantiate(Ex)
    # wir erhalten Punkt x mit Bbxb und Baxa
    p.deduce_left(Px)
    p.deduce_right(Px)
    A61 = p.modus_ponens(p.specialise(axioms[5], (a,x)))
    A62 = p.modus_ponens(p.specialise(axioms[5], (b,x)))
    Eq = p.substitute_equal(A61, Equal(a,b), A62)
    return p.directproof(Eq)

@theorem(ForAll((1,2,3,4), Between(1,2,4) & Between(2,3,4) >
                           Between(1,2,3)))
def Thm_3_5_1():
    """
     1--2-----4
        2--3--4
    ============
     1--2--3
    """
    a,b,c,d = p.start_context_names('abcd')
    p.assume(Between(a,b,d) & Between(b,c,d))
    (x,), BbxbBcxa = p.instantiate(
        p.modus_ponens(
            p.specialise(axioms[6], (a,b,b,c,d))))
    p.deduce_left(BbxbBcxa)
    x_eq_b = p.modus_ponens(p.specialise(axioms[5], (b,x)))
    p.substitute_equal(p.deduce_right(BbxbBcxa), Between(c,b,a), x_eq_b)
    return p.directproof(p.modus_ponens(p.specialise(Thm_3_2, (c,b,a))))

@theorem(ForAll((1,2,3,4), Between(1,2,3) & Between(1,3,4) >
                           Between(2,3,4)))
def Thm_3_6_1():
    """"""
    a,b,c,d = p.start_context_names('abcd')
    p.assume(Between(a,b,c))
    p.assume(Between(a,c,d))
    p.conjunction(
        p.modus_ponens(p.specialise(Thm_3_2, (a,c,d))),
        p.modus_ponens(p.specialise(Thm_3_2, (a,b,c))))
    p.modus_ponens(p.specialise(Thm_3_5_1, (d,c,b,a)))
    return p.directproof(p.modus_ponens(p.specialise(Thm_3_2, (d,c,b))))

@theorem(ForAll((1,2,3,4), Between(1,2,3) & Between(2,3,4) & -Equal(2,3) > Between(1,3,4)))
def Thm_3_7_1():
    """"""
    a,b,c,d = p.start_context_names('abcd')
    Babc = p.assume(Between(a,b,c))
    Bbcd = p.assume(Between(b,c,d))
    b_neq_c = p.assume(-Equal(b,c))

    (x,), BC = p.instantiate(p.specialise(axioms[3], (a,c,c,d)), 'x')
    Bacx = p.deduce_left(BC)
    p.conjunction(Babc, Bacx)
    Bbcx = p.modus_ponens(p.specialise(Thm_3_6_1, (a,b,c,x)))
    p.specialise(Thm_2_1, (c,d))
    p.deduce_right(BC)
    th = p.specialise(Thm_2_12, (b,c,c,d,x,d))
    p.auto_conjunction(th.left)
    x_eq_d = p.modus_ponens(th)
    p.substitute_equal(Bacx, Between(a,c,d), x_eq_d)
    return p.directproof(Between(a,c,d))

@theorem(ForAll((1,2,3,4), Between(1,2,4) & Between(2,3,4) >
                           Between(1,3,4)))
def Thm_3_5_2():
    """"""
    a,b,c,d = p.start_context_names('abcd')
    A1 = p.assume(Between(a,b,d))
    p.assume(Between(b,c,d))
    p.start_context(0)
    p.substitute_equal(A1, Between(a,c,d), p.assume(Equal(b,c)))
    p.directproof(Between(a,c,d))
    p.start_context(0)
    p.assume(-Equal(b,c))
    th = p.specialise(Thm_3_5_1, (a,b,c,d))
    p.auto_conjunction(th.left)
    p.modus_ponens(th)
    th = p.specialise(Thm_3_7_1, (a,b,c,d))
    p.auto_conjunction(th.left)
    p.modus_ponens(th)
    p.directproof(Between(a,c,d))
    p.tertium_non_datur(Equal(b,c))
    p.disjunction_elimination(Equal(b,c), -Equal(b,c), Between(a,c,d))
    return p.directproof(Between(a,c,d))

@theorem(ForAll((1,2,3,4), Between(1,2,3) & Between(1,3,4) >
                           Between(1,2,4)))
def Thm_3_6_2():
    """"""
    a,b,c,d = p.start_context_names('abcd')
    p.assume(Between(a,b,c))
    p.assume(Between(a,c,d))
    p.conjunction(
        p.modus_ponens(p.specialise(Thm_3_2, (a,c,d))),
        p.modus_ponens(p.specialise(Thm_3_2, (a,b,c))))
    p.modus_ponens(p.specialise(Thm_3_5_2, (d,c,b,a)))
    return p.directproof(p.modus_ponens(p.specialise(Thm_3_2, (d,b,a))))

@theorem(ForAll((1,2,3,4), Between(1,2,3) & Between(2,3,4) & -Equal(2,3) > Between(1,2,4)))
def Thm_3_7_2():
    """"""
    a,b,c,d = p.start_context_names('abcd')
    p.assume(Between(a,b,c))
    p.assume(Between(b,c,d))
    p.assume(-Equal(b,c))
    p.modus_ponens(p.specialise(Thm_3_2, (a,b,c)))
    p.modus_ponens(p.specialise(Thm_3_2, (b,c,d)))
    p.modus_ponens(p.specialise(symmetry_inequal, (b,c)))

    th = p.specialise(Thm_3_7_1, (d,c,b,a))
    p.auto_conjunction(th.left)
    p.modus_ponens(th)
    p.modus_ponens(p.specialise(Thm_3_2, (d,b,a)))
    return p.directproof(Between(a,b,d))


@theorem(Exists((1,2), -Equal(1,2)))
def Thm_3_13():
    """There are at least two distinct points"""
    p.start_context(0)
    (a,b,c), D = p.instantiate(axioms[7], 'abc')
    p.deduce_right(D)
    p.start_context(0)
    p.substitute_equal(-Between(c,a,b), -Between(c,a,a), p.assume(Equal(a,b)))
    p.specialise(Thm_3_1, (c,a))
    contradiction = p.conjunction(Between(c,a,a),-Between(c,a,a))
    p.directproof(contradiction)
    p.non_contradiction(Between(c,a,a))
    p.modus_tollens(Equal(a,b), contradiction)
    return p.directproof(p.generalize((a,b), -Equal(a,b)))

@theorem(ForAll((1,2), Exists((3,), Between(1,2,3) & -Equal(2,3))))
def Thm_3_14():
    """lines can be extended"""
    a,b = p.start_context_names('ab')
    (u,v), neq = p.instantiate(Thm_3_13, 'uv')
    (c,), con = p.instantiate(p.specialise(axioms[3], (a,b,u,v)), 'c')
    p.deduce_all(con)
    p.start_context(0)
    p.substitute_equal(Congruent(b,c,u,v), Congruent(b,b,u,v), p.assume(Equal(b,c)))
    p.modus_ponens(p.specialise(Thm_2_2, (b,b,u,v)))
    p.modus_ponens(p.specialise(axioms[2], (u,v,b)))
    p.directproof(Equal(u,v))
    p.modus_tollens(Equal(b,c), Equal(u,v))
    con = p.conjunction(Between(a,b,c), -Equal(b,c))
    return p.directproof(p.generalize((c,), con))


@theorem(ForAll((1,2,3,4,5,6), Between(1,2,3) & Between(4,5,3) & Between(1,6,4)
    > Exists((7,), Between(6,7,3) & Between(2,7,5))))
def Thm_3_17():
    """Sei 1,4,3 ein Dreieck mit 5 auf der Seite 43 und 2 auf der Seite 31,
       und 6 auf der Seite 14. Dann gibt es einen Punkt 7 der auf der Strecke
       25 und auf der Strecke 63 liegt.
    """
    a,b,c,a1,b1,p_ = p.start_context_names(['a','b','c',"a'", "b'", 'p'])
    p.assume(Between(a,b,c))
    p.assume(Between(a1,b1,c))
    p.assume(Between(a,p_,a1))
    p.modus_ponens(p.specialise(Thm_3_2, (a1,b1,c)))
    p.modus_ponens(p.specialise(Thm_3_2, (a,b,c)))
    p.conjunction(Between(a,p_,a1), Between(c,b1,a1))
    (x,), C = p.instantiate(p.modus_ponens(p.specialise(axioms[6], (a,c,p_,b1,a1))), 'x')
    p.deduce_right(C)
    p.conjunction(Between(b1,x,a), Between(c,b,a))
    (q,), D = p.instantiate(p.modus_ponens(p.specialise(axioms[6], (b1,c,x,b,a))), 'q')
    p.conjunction(p.deduce_left(C), p.deduce_left(D))
    q_prop = p.conjunction(
        p.modus_ponens(p.specialise(Thm_3_5_2, (p_,x,q,c))),
        p.deduce_right(D))
    return p.directproof(p.generalize((q,), q_prop))

def IFS(a,b,c,d,a1,b1,c1,d1):
    """inner five segment configuration"""
    return (Between(a,b,c) & Between(a1,b1,c1) &
        Congruent(a,c,a1,c1) &
        Congruent(b,c,b1,c1) &
        Congruent(a,d,a1,d1) &
        Congruent(c,d,c1,d1))

@theorem(ForAll((1,2,3,4,5,6,7,8), IFS(1,2,3,4,5,6,7,8) > Congruent(2,4,6,8)))
def Thm_4_2():
    """inner five segment congruence"""
    a,b,c,d,a1,b1,c1,d1 = p.start_context_names(['a','b','c','d',"a'","b'","c'","d'"])
    p.deduce_all(p.assume(IFS(a,b,c,d,a1,b1,c1,d1)))
    p.start_context(0)
    p.assume(Equal(a,c))
    p.substitute_equal(Congruent(a,c,a1,c1), Congruent(a,a,a1,c1), Equal(a,c))
    p.modus_ponens(p.specialise(Thm_2_2, (a,a,a1,c1)))
    p.modus_ponens(p.specialise(axioms[2], (a1,c1,a)))

    p.substitute_equal(Between(a,b,c), Between(c,b,c), Equal(a,c))
    p.substitute_equal(Between(a1,b1,c1), Between(c1,b1,c1), Equal(a1,c1))
    p.modus_ponens(p.specialise(axioms[5], (c,b)))
    p.modus_ponens(p.specialise(axioms[5], (c1,b1)))
    p.substitute_equal(Congruent(c,d,c1,d1),Congruent(b,d,c1,d1),Equal(c,b))
    p.substitute_equal(Congruent(b,d,c1,d1),Congruent(b,d,b1,d1),Equal(c1,b1))
    p.directproof(Congruent(b,d,b1,d1))
    p.start_context(0)
    p.assume(-Equal(a,c))
    (e,), con = p.instantiate(p.specialise(Thm_3_14, (a,c)), 'e')
    p.deduce_all(con)
    (e1,), con = p.instantiate(p.specialise(axioms[3], (a1,c1,c,e)), ["e'"])
    p.deduce_all(con)
    show_congruent(p, c,e,c1,e1)
    show_congruent(p, e,c,e1,c1)
    show_congruent(p, c,b,c1,b1)
    p.auto_conjunction(AFS(a,c,e,d,a1,c1,e1,d1))
    impl = p.specialise(axioms[4], (a,c,e,d,a1,c1,e1,d1))
    p.auto_conjunction(impl.left)
    p.modus_ponens(impl)
    impl = p.specialise(Thm_3_6_1, (a,b,c,e))
    p.auto_conjunction(impl.left)
    p.modus_ponens(impl)
    p.modus_ponens(p.specialise(Thm_3_2, (b,c,e)))
    impl = p.specialise(Thm_3_6_1, (a1,b1,c1,e1))
    p.auto_conjunction(impl.left)
    p.modus_ponens(impl)
    p.modus_ponens(p.specialise(Thm_3_2, (b1,c1,e1)))
    p.modus_ponens(p.specialise(symmetry_inequal, (c,e)))
    impl = p.specialise(axioms[4], (e,c,b,d,e1,c1,b1,d1))
    p.auto_conjunction(impl.left)
    p.modus_ponens(impl)
    p.directproof(Congruent(b,d,b1,d1))
    p.tertium_non_datur(Equal(a,c))
    return p.directproof(p.disjunction_elimination(Equal(a,c), -Equal(a,c), Congruent(b,d,b1,d1)))
