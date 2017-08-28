from itertools import count
from heapq import heappop, heappush, heapify

SRC_HINT = object()
SRC_GENERATOR = object()

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


class FreeTerm(Term):
    def __init__(self, ctx, hint=None):
        self.hint = hint
        self.ctx = ctx
        
    def __str__(self):
        return self.ctx.get_name(self, self.hint)

class TermContext(object):
    def __init__(self):
        self._names = {}
        self._used_names = {}
        self._free_names = []
        self._gen_names = iter(free_term_symbols())
        self._discarded = set()
        
    def get_name(self, var, hint=None):
        if var in self._discarded:
            raise ValueError('reusing discarded variable')
        if var not in self._names:
            if hint and hint not in self._used_names:
                if hint in self._free_names:
                    self._free_names.remove(hint)
                    heapify(self._free_names)
                name = hint
                src = SRC_HINT
            elif self._free_names:
                name = heappop(self._free_names)
                src = SRC_GENERATOR
            else:
                name = next(self._gen_names)
                while name in self._names:
                    name = next(self._gen_names)
                src = SRC_GENERATOR
            assert name not in self._used_names
            self._names[var] = name
            self._used_names[name] = src
        return self._names[var]
    
    def discard(self, var):
        if var in self._discarded:
            raise ValueError('cannot discard again')
        if var in self._names:
            name = self._names[var]
            self._discarded.add(var)
            src = self._used_names.pop(name)
            if src is SRC_GENERATOR:
                heappush(self._free_names, self._names[var])
            del self._names[var]
            

'''first order logic formulas'''

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
        if terms:
            return UniversalQuantifier(terms, self)
        else:
            return self

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
        new_names = (t for t in bound_term_symbols() if t not in names.values())
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
        new_names = (t for t in bound_term_symbols() if t not in names.values())
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
