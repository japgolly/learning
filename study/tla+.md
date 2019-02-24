HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

[]X means X is always true

[]HCnxt       means  [hr=10] -> [hr=11] -> [hr=12] -> [hr=1] etc
[][HCnxt]_hr  means  [hr=10] -> [hr=11] -> [hr=11] -> [hr=12] etc
              = []HCnxt \/ [hr' = hr]


A temporal formula satised by every behavior is called a theorem, so HC => []HCini should be a theorem.

extends Naturals
^^ use natural numbers, have + - * etc apply to nats

extends Sequences
^^ list ops over tuples

Good idea to declaure all type invariants.
But don't make it part of the spec as an assumption/invariant, imply it. Assert it as a theorem.

TypeInvariants == /\ val \in Data
                  /\ rdy \in {0,1}
                  /\ ack \in {0,1}

TypeInvariants ==
  /\ val \in Data
  /\ rdy \in {0,1}
  /\ ack \in {0,1}

Step conditions should just be conjucts (rather that implication)
UNCHANGED ack is the same as ack' = ack

record types  [ k :   T , … ]
record values [ k |-> v , … ]

[ record EXCEPT !.k = v, … ]
[ chan EXCEPT !.ack = 1 - @ ] where @ becomes chan.ack

Data Val
NoVal == CHOOSE v : v /= Val

[ x \in A |-> x + 1 ] is the same as (x: A) => x + 1
[ a |-> b, c |-> d ] is the same as { case a => b; case c => d }

□  = continuously
◇  = eventually
□◇ = infinitely occurring (eg. ABABABABABAB..)
◇□ = eventually becomes true and stays true continuously
⤳  = leads to. F ⤳ G = □(F ⇒ ◇G)

weak fairness:
* If A ever becomes CONTINUOUSLY enabled, then an A step must eventually occur.
* A cannot REMAIN enabled forever without another A step occurring.

strong fairness:
* If A ever becomes REPEATEDLY enabled, then an A step must eventually occur.
* A cannot BE REPEATEDLY enabled forever without another A step occurring.

Fairness - X has to happen




Idea: could break my problem into 2...
  1) (user <-> webapp) props (redis agnostic)
  2) (webapp <-> redis) props
