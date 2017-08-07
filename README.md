# Tarski
Formal theorem verification in Python with Tarskis Axioms for elementary Geometry as an example application.

The proof has to be written in the program, and each step is verified.
Currently there is no search for a proof implemented.

Reference
---------
Wolfram Schwabhäuser, Wanda Szmielew, Alfred Tarski: "Metamathematische Methoden in der Geometrie", Springer 1983, 978-3-540-12958-5

See also
--------
* [Tarski's Axioms (Wikipedia)](https://en.wikipedia.org/wiki/Tarski%27s_axioms)
* [First-Order Logic (Wikipedia)](https://en.wikipedia.org/wiki/First-order_logic)

Program Overview
----------------
<dl>
<dt>formula.py:</dt>
<dd>Expression of first-order logic formulas</dd>

<dt>proof.py:</dt>
<dd>The proof verifier.
    A class keeping known true sentences and implementing rules of inference.</dd>
    
<dt>tarski.py:</dt>
<dd>Tarskis predicates `Between` and `Congruent`. 
    Tarskis axioms.</dd>

<dt>main.py:</dt>
<dd>Proofs of theorems based on the axioms written using the proof verifier</dd>
</dl>
    

