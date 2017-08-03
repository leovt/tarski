from formula import (Predicate, 
                     Term,
                     UniversalQuantifier as ForAll,
                     ExistentialQuantifier as Exists)

Equal = Predicate('Equal', 2, '{} = {}')
Congruent = Predicate('Congruent', 4, '{}{}~{}{}')
Between = Predicate('Between', 3, '({1} in {0}{2})')

x,y,r,s,t,u = Term(), Term(), Term(), Term(), Term(), Term()
x1,y1,r1,s1 = 1,2,3,4
axioms = [
    ForAll((x,y), Congruent(x,y,y,x)),
    ForAll((x,y,r,s,t,u), Congruent(x,y,r,s) & Congruent(x,y,t,u) > Congruent(r,s,t,u)),

    # Identitätsaxiom für die Streckenkongruenz
    ForAll((x,y,r), Congruent(x,y,r,r) > Equal(x,y)),

    # Axiom der Streckenabtragung
    ForAll((y,r,s,t), Exists((x,), Between(y,r,x) & Congruent(r,x,s,t))),
    
    # Fünf-Strecken-Axiom
    ForAll((x,y,r,s,x1,y1,r1,s1),
           -Equal(x,y) &
           Between(x,y,r) & Between(x1,y1,r1) &
           Congruent(x,y,x1,y1) &
           Congruent(y,r,y1,r1) &
           Congruent(x,s,x1,s1) &
           Congruent(y,s,y1,s1) 
           > Congruent(r,s,r1,s1)),

    # Identitätsaxiom für die Zwischenbeziehung
    ForAll((x,y), Between(x,y,x) > Equal(x,y)),
    
    # Axiom von Pasch, innere Form
    ForAll((x,y,r,s,t), Between(x,r,t) & Between(x,s,t) > Exists((u,), Between(r,u,y) & Between(s,u,x))),

    # unteres Dimensionsaxiom
    Exists((r,s,t), -Between(r,s,t) & -Between(s,t,r) & -Between(t,r,s)),
    
    # oberes Dimensionsaxiom
    ForAll((x,y,r,s,t), 
           -Equal(x,y) &
           Congruent(r,x,r,y) & Congruent(s,x,s,y) & Congruent(t,x,t,y) 
           > Between(r,s,t) | Between(s,t,r) | Between(t,r,s)),
          
    # Euklidisches Axiom
    ForAll((r,s,t,u,x),
           -Equal(r,u) &
           Between(r,u,x) & Between(s,u,t) 
           > Exists((x1,y1), Between(r,s,x1) & Between(r,t,y1) & Between(x1,x,y1))),
    
    # Stetigkeit
    ]


