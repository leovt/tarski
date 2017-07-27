from formula import (Predicate, 
                     Term,
                     UniversalQuantifier as ForAll,
                     ExistentialQuantifier as Exists)

Equal = Predicate('Equal', 2, '{} = {}')
Congruent = Predicate('Congruent', 4, '{}{}~{}{}')
Between = Predicate('Between', 3, '({1} in {0}{2})')

x,y,r,s,t,u = Term(), Term(), Term(), Term(), Term(), Term()
str(x),str(y),str(r),str(s),str(t),str(u)

axioms = [
    ForAll((x,y), Congruent(x,y,y,x)),
    ForAll((x,y,r,s,t,u), Congruent(x,y,r,s) & Congruent(x,y,t,u) > Congruent(r,s,t,u)),
    ForAll((x,y,r), Congruent(x,y,r,r) > Equal(x,y)),

    ForAll((x,y), Between(x,y,x) > Equal(x,y)),
    ForAll((x,y,r,s,t), Between(x,r,t) & Between(x,s,t) > Exists((u,), Between(r,u,y) & Between(s,u,x))),
    #continuity missing
    Exists((r,s,t), -Between(r,s,t) & -Between(s,t,r) & -Between(t,r,s)),
    ForAll((x,y,r,s,t), Congruent(r,x,r,y) & Congruent(s,x,s,y) & Congruent(t,x,t,y) > Between(r,s,t) | Between(s,t,r) | Between(t,r,s)),
    ]


