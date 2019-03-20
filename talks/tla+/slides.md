---
title: TLA+
# theme: simple
highlightTheme: 'tomorrow-night-bright'
revealOptions:
  controls: false
  width: 1440
  height: 810
  transition: 'none'
  transitionSpeed: 'fast'

---

# Something-something-<span style="color:#c33">TLA+<span>

---

* Not my usual talk
* ~~FP, types, Scala~~
* No slides
* Most slides are for me <span style="opacity:0.4">*(don't read!)*<span>

---

## usual tools

* expressive types / Curry-Howard(-Lambek)
* FP
* "FP structures / stdlib"
  * {co,}{monad,traverse,blah³}
  * recursion schemes
* property testing
* benchmarking & profiling

---

distributed/concurrent algos
<br><br>
hole in toolbelt

---

### Story begins...

1. Excuse
1. ShipReq
1. 2½ days (beginner + benefit)

---

## What is TLA+?

* spec
* universe
* level of abstraction / relevant / -trivial
* code gen
* PlusCal
* MC / PS

---

## Canonical ticking clock example

<br>
```
Spec == Init /\ [][Next]_vars
THEOREM Spec => []Invariants
```

---

- consts, vars
- props, indentation, types
- classical logic
- set theory
- modules
- model da pipez!

---

- safety vs liveness
- stuttering & fairness
- temporal logic

---

```
       □rich - royalty
       ◊rich - lotto winner
      ◊□rich - jeff bezos
      □◊rich - eccentric entrepreneur
```

---

# My Need/Excuse

* What I did
* What I learned

---

<p class="stretch">
<a href=shipreq-arch.jpg><img src=shipreq-arch.jpg /></a>
</p>

---

`shipreq_users.tla`

<br>

* Run TLC
* demo constants
* print states
* symmetry sets

---

# Why / Questions

* eventual consistency
  * not: "occasional" eventual consistency
  * not: "95%" eventual consistency
  * even if everything that can go wrong, does
* distributed atomicity / txns
* no deadlocks / infinite loops / races
* cache invalidation is hard; no stale data

---

# Why / Questions

* Traffic/CPU/time optimisation:
  * occasional snapshots
  * event sequence tails
  * correctness

---

## abstraction level

Irrelevant / orthogonal:

* event content
* other projects
* network retry _(!failure)_

---

<p class="stretch">
<a href=shipreq-algo.svg><img src=shipreq-algo.svg /></a>
</p>

---

# the model

`model.scala`

`project.tla`

---

```
UpdateRespond ==
  \/ Update_ReadRedis
  \/ Update_ReadDb
  \/ Update_WriteRedis1
  \/ Update_WriteDb
  \/ Update_WriteRedis2
  \/ Update_Respond

Action ==
  \/ UserConnect
  \/ UserDisconnect
  \/ UpdateRequest
  \/ UpdateRespond
  \/ Publish
```

---

```c
Fairness ==
  /\ WF_vars(UpdateRespond)
  /\ SF_vars(UpdateRespond)
  /\ SF_vars(Publish)

Spec == Init /\ [][Action]_<<vars>> /\ Fairness
```

---

_Fairness: X has to happen_

<br>
**weak fairness:**
* If A ever becomes CONTINUOUSLY enabled, then an A step must eventually occur.
* A cannot REMAIN enabled forever without another A step occurring.

<br>
**strong fairness:**
* If A ever becomes REPEATEDLY enabled, then an A step must eventually occur.
* A cannot BE REPEATEDLY enabled forever without another A step occurring.

---

* I deliberately added a bug in publish - didn't fail!
* be suspicious
* branch coverage

---

* success!
* found a bug in `WriteDB` → `WriteRedis2` (cache magically already up-to-date)
* found a bug in `WriteDB` → `ReadRedis` (infinite loop)
* still running after an hour

---

# Curbing ∞

* hr = <span style="color:red">1</span>,2,3,4,5,6,7,8,9,10,11,12,<span style="color:red">1</span>,...
* db.ver = 1,2,3,...,500,501,...,7034,7035,...

---

# Curbing ∞

* problem
* solution #1

```
+------------------+      +------------------+
| db: 7            |      | db: 4            |
| redis:           |      | redis:           |
|   snapshot: 4    |      |   snapshot: 1    |
|   events  : 5..7 |  =>  |   events  : 2..4 |
| users:           |      | users:           |
|   [0]: 7         |      |   [0]: 4         |
|   [1]: 7         |      |   [1]: 4         |
+------------------+      +------------------+
```

---

# Curbing ∞

* solution #2
* `shipreq.tla`
  * `Next == Act \/ React`
  * `CONSTRAINT MCContinue`
  * `FinalInvariants == MCDone => AllUsersUpToDate`
* `shipreq.cfg`


---

When to snapshot?

Who cares!

Have TLC split into two timelines

---

## Model the universe!

* RedisEviction

---

## Model the universe!

* Worker death *(...oh crap...)*
  * Forgot about WorkerDeath
  * "Already 'finished' spec, will take ages / effort!"

---

```tla+
WebappDeath ==
  \* Remember user isn't a person/account; it's a browser tab, a session
  /\ \E affectedUsers \in (SUBSET(OnlineUsers) \ {{}}) :
    /\ userState' = [u \in User |-> IF u \in affectedUsers
                                    THEN [userState[u] EXCEPT !.online = FALSE, !.reqs = {}]
                                    ELSE userState[u]]
    /\ procs' = {p \in procs : p.user \notin affectedUsers}
    /\ pub' = {usrEvt \in pub : usrEvt[1] \notin affectedUsers}
    /\ UNCHANGED << db, redis >>
```

7 LoC, 1 comment, <5 min

---

Run model

* (N/2/2/3) ~4 sec
* introduce bug (`Update_WriteRedis2`)

---

```
+------------+-------+------+-----+-------------+
| disconnect | users | reqs | ver |        time |
+------------+-------+------+-----+-------------+
|          N |     2 |    2 |   3 |          4s |
|            |       |      |   4 |         17s |
|            |       |      |   5 |      2m 51s |
|            |       |      |   6 |     26m 50s |
+------------+-------+------+-----+-------------+
|          N |     2 |    3 |   3 |      1m 57s |
|            |       |      |   4 |     43m 54s |
|            |       |      |   5 | 14h 10m  0s |
+------------+-------+------+-----+-------------+
|          Y |     2 |    2 |   3 |     40m  0s |
+------------+-------+------+-----+-------------+
```

---

# Q: How useful is this in practice?

A: Extremely!

Finds crazy bugs that you'd never catch on your own...

Two examples:

---
<div style="font-size:60%; white-space:pre; text-align:left; display:flex">
<div style="padding-right:4em">State  1: Initial predicate
State  2: UserConnect
State  3: Load_ReadRedis
State  4: Load_ReadDB
State  5: Load_WriteRedis
State  6: Load_Respond
State  7: UpdateRequest
State  8: Update_ReadRedis
State  9: Update_WriteDB
State 10: WebappDeath
State 11: UserConnect
</div>
<div>State 12: Load_ReadRedis
State 13: RedisEviction
State 14: Load_Respond
State 15: UpdateRequest
State 16: Update_ReadRedis
State 17: Update_ReadDB
State 18: Update_WriteRedis1
State 19: Update_WriteDB
State 20: Update_WriteRedis2
State 21: Update_Respond
State 22: Publish
</div></div>

<div style="font-size:50%; white-space:pre; text-align:left; font-family:monospace">
/\ db        = [ver |-> 3]
/\ redis     = [ver |-> 3, events |-> {}]
/\ procsL    = {}
/\ procsU    = {}
/\ pub       = {}
/\ userState = (u1 :> [ver |-> 1, status |-> "active", future |-> {3}, reqs |-> {}])
<div>

---

Imagine a bug report describing this, then having to track it down!

*"We keep getting reports that users randomly stop getting updates and can't see their changes."*

---

Another example error:
* 2+ servers
* User #1 connects via Server #1
* User #2 connects via Server #2
* User #1 makes a change
* Server #1 crashes just after a successful write to the DB
* Either...
  * User #1 loses WebSocket, reconnects, gets latest version, fine
  * They ragequit and never connect again
* User #2 never receives the change because it wasn't published to the topic

---

* With TLC
  * these errors are caught on every single run (deterministic & exhaustive)
  * usually < 1 sec to catch
  * the happenings of the entire universe from start to crash, on one screen

---

1. Summary
1. Full spec (if time)

---

# summary

* Very practical!
* (Would've saved a few Telstra days)
* Great investment of time!
* toolbelt++
* super fast to revise (eg. cache eviction)
* super easy to model real-life trouble / rare cases

---

# Not perfect

* Abysmal stdlib
* Not sure how to test efficiency...<br>Eg. bug that results in 90% cache misses
* Model checking can be slow
* Sometimes hard to ensure correctness

<span style="opacity:0.5">*(still a huge improvement though)*</span>

---

# Next?

* Alloy
* Provers

---

# Hydrate yourself now!

`project.tla`
