from formula import (Predicate, 
                     Term,
                     UniversalQuantifier as ForAll,
                     ExistentialQuantifier as Exists, BinaryConnective)
from itertools import count

Equal = Predicate('Equal', 2, '{} = {}')
Congruent = Predicate('Congruent', 4, '{}{}~{}{}')
Between = Predicate('Between', 3, '({1} in {0}{2})')

x,y,r,s,t,u = Term(), Term(), Term(), Term(), Term(), Term()
str(x),str(y),str(r),str(s),str(t),str(u)

class DictStack(dict):
    def __init__(self, parent=None):
        dict.__init__(self)
        self._parent = parent

    def __missing__(self, key):
        if self._parent is None:
            raise KeyError(key)
        return self._parent[key]

    def push(self):
        return DictStack(self)

    def pop(self):
        assert self._parent is not None
        return self._parent

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

class ProofContext():
    def __init__(self):
        self.fact_number = count(1)
        self.facts = DictStack()
        self.freevars = []
        self.assumptions = []
        
        for axiom in axioms:
            self._add(axiom, 'Axiom')

    def _add(self, fact, justification, references=(), evidence=None):
        assert fact not in self.facts
        assert all(any(x in y for y in self.freevars) for x in fact.free())
        try:
            [self.facts[r] for r in references]
        except KeyError as e:
            assert False, 'Missing Fact %s' % (e.args)
        number = next(self.fact_number)
        self.facts[fact] = (fact, number, justification, references, evidence)
        if not references:
            ref = ''
        else:
            ref = '(%s)' % ', '.join(str(self.facts[r][1]) for r in references)
        print(number, '  '*len(self.assumptions), fact, justification, ref)

    def start_context(self, number_of_variables):
        variables = [Term() for i in range(number_of_variables)]
        self.facts = self.facts.push()
        self.freevars.append(variables)
        self.assumptions.append([])
        return variables

    def assume(self, fact):
        self.assumptions[-1].append(fact)
        self._add(fact, 'assumption', [])
        return fact

    def directproof(self, fact):
        assump = self.assumptions.pop()
        freevars = self.freevars.pop()
        assert fact in self.facts

        if not assump:
            new_fact = fact
        else:
            conditions = assump[0]
            for x in assump[1:]:
                conditions = BinaryConnective(conditions, '&', x)
            new_fact = BinaryConnective(conditions, '->', fact)
        new_fact = new_fact.generalize(freevars)
        evidence = dict(self.facts)
        self.facts = self.facts.pop()
        self._add(new_fact, 'direct proof', (), evidence)
        return new_fact

    def specialise(self, fact, subs):
        new_fact = fact
        for i,s in reversed(list(enumerate(subs))):
            new_fact = new_fact.specialise(i, s)
        self._add(new_fact, 'universal specialisation', [fact])
        return new_fact

    def conjunction(self, left, right):
        new_fact = BinaryConnective(left, '&', right)
        self._add(new_fact, 'conjunction', (left, right))
        return new_fact

    def modus_ponens(self, implication):
        assert implication.connective == '->'
        self._add(implication.right, 'modus ponens', (implication, implication.left))
        return implication.right

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
