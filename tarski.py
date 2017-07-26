from itertools import count

def bound_term_symbols():
    for s in 'xyrstuvwz':
        yield s
    for i in count(2):
        yield 'x%d'%i

def free_term_symbols():
    for s in 'abcdefghijklmnopq':
        yield s
    for i in count(2):
        yield 'a%d'%i
    

class SymbolMap(dict):
    def __init__(self):
        dict.__init__(self)
        self._term_symbols = free_term_symbols()

    def __missing__(self, key):
        value = self[key] = next(self._term_symbols)
        return value

symbol_map = [SymbolMap()]

class Term(object):
    def __str__(self):
        return symbol_map[-1][self]

class BoundTerm(Term):
    def __init__(self, quantifier):
        self.quantifier = quantifier

class Formula(object):
    def substitute(self, subs):
        subs = {x:t for x,t in subs.items() if x in self.free()}
        assert not any(t in self.bound() for x,t in subs.items())
        return self._substitute(subs)

    def serialize(self):
        free = list(self.free())
        bound = list(self.bound())

        variables = free+bound
        varids = {v:i for i,v in enumerate(variables)}

        return (len(free), len(bound), self._serialize(varids))

    def generalize(self, terms):
        return UniversalQuantifier(terms, self)

    def __str__(self):
        names = {x:str(x) for x in self.free()}
        return self._string(names)

    def __eq__(self, other):
        return self.free()==other.free() and self.serialize() == other.serialize()

    def __hash__(self):
        return hash(self.serialize())

    def __and__(self, other):
        return BinaryConnective(self, '&', other)

    def __or__(self, other):
        return BinaryConnective(self, '|', other)

    def __gt__(self, other):
        return BinaryConnective(self, '->', other)

    def __neg__(self):
        return Negation(self)


class Predicate(object):
    def __init__(self, name, arity, fmt):
        self.name = name
        self.arity = arity
        self.fmt = fmt
    def __call__(self, *args):
        assert len(args) == self.arity
        return PredicateFormula(self, *args)

Equal = Predicate('Equal', 2, '{} = {}')
Congruent = Predicate('Congruent', 4, '{}{}~{}{}')
Between = Predicate('Between', 3, '({1} in {0}{2})')

class OrderedFrozenSet(tuple):
    def __new__(cls, items=()):
        filtered = []
        for x in items:
            if x in filtered:
                continue
            filtered.append(x)
        return tuple.__new__(cls, filtered)

    def __and__(self, other):
        return OrderedFrozenSet([x for x in self if x in other])

    def __or__(self, other):
        return OrderedFrozenSet(self + other)

    def __sub__(self, other):
        return OrderedFrozenSet([x for x in self if x not in other])
    

class PredicateFormula(Formula):
    def __init__(self, predicate, *terms):
        self.predicate = predicate
        self.terms = terms

    def _string(self, names):
        return self.predicate.fmt.format(*(names[x] for x in self.terms))

    def __repr__(self):
        return '%s(%s)' % (self.predicate.name, ', '.join(map(repr, self.terms)))

    def free(self):
        return OrderedFrozenSet(self.terms)

    def bound(self):
        return OrderedFrozenSet()

    def _substitute(self, subs):
        return PredicateFormula(self.predicate, *tuple(subs.get(x,x) for x in self.terms))

    def _serialize(self, varids):
        return ('Pred', self.predicate.name, tuple(varids[x] for x in self.terms))

class Negation(Formula):
    def __init__(self, formula):
        self.formula = formula

    def _string(self, names):
        return '!%s' % (self.formula._string(names),)

    def __repr__(self):
        return 'Negation(%r)' % (self.formula,)

    def free(self):
        return self.formula.free()

    def bound(self):
        return self.formula.bound()

    def _substitute(self, subs):
        return Negation(self.formula.substitute(subs))

    def _serialize(self, varids):
        return ('Neg', self.formula._serialize(varids))

class BinaryConnective(Formula):
    def __init__(self, left, connective, right):
        self.left = left
        self.connective = connective
        self.right = right

    def _string(self, names):
        return '(%s %s %s)' % (self.left._string(names), self.connective, self.right._string(names))
        
    def __repr__(self):
        return '(%r %s %r)' % (self.left, self.connective, self.right)

    def free(self):
        return self.left.free() | self.right.free()

    def bound(self):
        return self.left.bound() | self.right.bound()
        
    def _substitute(self, subs):
        return BinaryConnective(self.left.substitute(subs), self.connective, self.right.substitute(subs))

    def _serialize(self, varids):
        return ('Bin', self.connective, self.left._serialize(varids), self.right._serialize(varids))

class UniversalQuantifier(Formula):
    def __init__(self, terms, formula):
        subs = {t:BoundTerm(self) for t in terms}
        self.terms = tuple(subs[t] for t in terms)
        self.formula = formula.substitute(subs)

    def _string(self, names):
        for b in self.terms:
            assert b not in names
        new_names = (t for t in bound_term_symbols() if t not in names)
        new_names_map = {b:t for b,t in zip(self.terms, new_names)}
        new_names_map.update(names)
        return 'A%s: %s' % (','.join(new_names_map[t] for t in self.terms), self.formula._string(new_names_map))

    def __repr__(self):
        return 'UniversalQuantifier((%s), %r)' % (','.join(map(repr,self.terms)), self.formula)

    def free(self):
        return self.formula.free() - self.terms

    def bound(self):
        return self.formula.bound() | self.terms

    def _substitute(self, subs):
        return UniversalQuantifier(self.terms, self.formula.substitute(subs))

    def _serialize(self, varids):
        return ('Uni', tuple(varids[x] for x in self.terms), self.formula._serialize(varids))

    def specialise(self, index, freevar):
        assert freevar not in self.bound()
        formula = self.formula.substitute({self.terms[index]:freevar})

        result = UniversalQuantifier(self.terms[:index] + self.terms[index+1:], formula)
        str(result)
        
        if len(self.terms) > 1:
            return result
        else:
            return formula
        
class ExistentialQuantifier(Formula):
    def __init__(self, terms, formula):
        subs = {t:BoundTerm(self) for t in terms}
        self.terms = tuple(subs[t] for t in terms)
        self.formula = formula.substitute(subs)

    def _string(self, names):
        for b in self.terms:
            assert b not in names
        new_names = (t for t in bound_term_symbols() if t not in names)
        new_names_map = {b:t for b,t in zip(self.terms, new_names)}
        new_names_map.update(names)
        return 'E%s: %s' % (','.join(new_names_map[t] for t in self.terms), self.formula._string(new_names_map))

    def __repr__(self):
        return 'ExistentialQuantifier((%s), %r)' % (','.join(map(repr,self.terms)), self.formula)

    def free(self):
        return self.formula.free() - self.terms

    def bound(self):
        return self.formula.bound() | self.terms

    def _substitute(self, subs):
        return ExistentialQuantifier(self.terms, self.formula.substitute(subs))

    def _serialize(self, varids):
        return ('Ex', tuple(varids[x] for x in self.terms), self.formula._serialize(varids))


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

ForAll = UniversalQuantifier
Exists = ExistentialQuantifier

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
