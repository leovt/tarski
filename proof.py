from formula import Term, BinaryConnective
from itertools import count

from tarski import axioms

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
