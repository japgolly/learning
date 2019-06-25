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

# From <span style="color:#c33">TLA+</span> to code

---

## Recap: What is TLA+ ?

* Temporal Logic of Actions (plus set theory)
* Formal spec of the universe
* State, transitions, invariants, liveness checks
* Model checking

```tla
VARIABLE h

Invariants == h \in 1..12
Init       == h \in 1..12
Next       == h' = (h % 12) + 1

Spec == Init /\ [][Next]_h
THEOREM Spec => [][Invariants]
```

---

## Why is it useful?

* Well-behaved ~~code~~ systems can be hard
  * Service interaction and coordination *(e2e it)*
  * Resource management *(eg WSClient)*
* Cache invalidation <!-- .element: class="fragment" -->
* Distributed atomicity / transactions <!-- .element: class="fragment" -->
* Consistency guarantees <!-- .element: class="fragment" -->
* Failure resilience / availability <!-- .element: class="fragment" -->

---

Why is it useful?

# THINKING

<div class="fragment" />

> Writing is nature's way of letting you know how sloppy your thinking is.

---

1. Write spec
2. Verify
3. <span style="color:red">???</span>
4. Ship amazing product
5. Profit

---

1. Write spec
2. Verify
3. <span style="color:#33bb33">&lt;share my experience&gt;</span>
4. Ship amazing product
5. Profit

---

1. Write spec
2. Verify
3. &lt;share my experience&gt;
4. Ship amazing product
5. <span style="color:red">??? *&#42;cries in Business&#42;*</span>
6. Profit

---

# Can TLA+ GENERATE CODE? OR DATA / MODELS? OR TESTS? NOT TO WOULD MEAN DUPLICATION AND DISASTER.

<span style="font-size:50%">let's see…</span>

---

## Background

<p class="stretch">
<a href=shipreq-arch.jpg><img src=shipreq-arch.jpg /></a>
</p>

---

### Spec Goals

1. Distributed cache
2. Eventual consistency
3. Data integrity
4. Termination
5. Failure resilience

---

### Actions

```tla
Act ==
  \/ UserConnect
  \/ UserDisconnect
  \/ UserReconnect
  \/ UpdateRequest
  \/ RedisEviction
  \/ WebappDeath
```

---

### Reactions

```tla
React ==
  \/ Load
  \/ Reload
  \/ UpdateRespond
  \/ RedisPublishEvent
  \/ SyncRequest
  \/ SyncPush
```

---

### Lets just look at a single slice

1. &nbsp; `UpdateRequest`
2. &nbsp; `UpdateRespond`
3. &nbsp; `RedisPublishEvent`

---

## Coding step 1:

I decided to start with Redis

---

```tla
VARIABLES redis, \* The state of Redis
          pub,   \* Set of events being published
          sub,   \* Users subscribed to event topic

TypeInvariants ==
  /\ redis \in [
       ver   : Nat,        \* snapshot ver; 0=none
       events: SUBSET Nat] \* event versions
  /\ pub \in SUBSET (User \X Nat)
  /\ sub \in SUBSET User
```

```scala
type Redis = {ver: Int, events: Set[Int]}
type Pub   = Set[(User, Int)]
type Sub   = Set[User]
```

---

<pre><code class="lang-tla hljs" data-trim data-noescape style="font-size:75%; margin-bottom:2em">
DataInvariants ==

  /\ \A u \in User : userState[u].status = "offline" => (u \notin sub)

  /\ redis.ver <= db.ver

  \* No gaps in Redis events
  /\ \A e \in redis.events :
       IF redis.ver > 0
       THEN (e - 1) \in (redis.events \union {redis.ver}) \* all events proceed snapshot
       ELSE (e - 1) \in (redis.events) \/ e = Min[redis.events]
</code></pre>

<div class="fragment" />

* Spec is more capable than code.
  Invariants about distributed entities at exact same time:
  * client & server/topic
  * redis & postgres

* Invariant #3 (Redis) *can* exist in code

---

How does this translate to code?

* `VARIABLE redis`
  * state exist in Redis
  * access from server

---

`Spec => Impl`

<div class="fragment" />

<br>
In programming: <br> `interface + laws => impl`

---

`Spec => Impl`

<br>
In programming: <br> `abstraction + laws => specialisation`

---


```tla
VARIABLE redis

TypeInvariant ==
  redis \in [
    ver   : Nat,        \* snapshot ver; 0=none
    events: SUBSET Nat] \* event versions
```

<br>

Scala equivalent:

```scala
var redis: RedisState
case class RedisState(ver: Int, events: Set[Int])
```

---

```scala
case class RedisState(ver   : Int,
                      events: Set[Int])
```

↑ is too abstract for real code

```scala
case class RedisState(snapshot: Option[Snapshot],
                      events  : Set[Event])
```

---

abstraction + laws => specialisation

```scala

case class Abstraction(ver   : Int,
                       events: Set[Int])


case class Specialisation(snapshot: Option[Snapshot],
                          events  : Set[Event]) {

  // Proof
  def abstractYoSelf = Abstraction(
    ver    = this.snapshot.fold(0)(_.ver),
    events = this.events.map(_.ver))
}
```

---

Next: Redis algebra

```scala
trait Redis[F[_]] {
  // umm.....
}
```

---

<pre><code class="lang-diff hljs" style="font-size:70%; line-height:1.2em" data-trim data-noescape>
+PublishEvents(events) ==
+  pub' = pub \union (sub \X events)
+
 RedisWriteSnapshot(ver, eventsToPublish, OnOk, OnFail) ==
   /\ IF ver > redis.ver
      THEN
<span style="color:#ff8">@@ -176,7 +183,7 @@ RedisWriteSnapshot(ver, eventsToPublish, OnOk, OnFail) ==</span>
        \* Redis has a more recent state than this proc
        /\ UNCHANGED redis
        /\ OnFail
-  /\ pub' = pub \union (sub \X eventsToPublish)
+  /\ PublishEvents(eventsToPublish)

 RedisWriteEvents(eventsToCache, eventsToCacheAndPublish, OnOk, OnFail) ==
   LET events     == eventsToCache \union eventsToCacheAndPublish
<span style="color:#ff8">@@ -191,7 +198,23 @@ RedisWriteEvents(eventsToCache, eventsToCacheAndPublish, OnOk, OnFail) ==</span>
           fail \* Gaps in redis.events prohibited
         ELSE
           apply
-     /\ pub' = pub \union (sub \X eventsToCacheAndPublish)
+     /\ PublishEvents(eventsToCacheAndPublish)
</code></pre>

<br>

Lesson! Just like in programming, use functions in TLA+ for reuse and separation.

---

```tla
PublishEvents(events) ==
  pub' = pub \union (sub \X events)
```

↓ ↓ ↓

```scala
trait Redis[F[_]] {

  def publishEvents(
    id: ProjectId,
    events: NonEmptySet[VerifiedEvent]): F[Unit]

}
```

---

*Show real Redis code*

---

Next I wanted an In-Memory implementation...

* testing
* performance testing
* running locally with less external deps

<br>

Usually takes <1hr; always a great investment

<br>

*Show code?*

---

How do I know I didn't make a mistake?
<br>Testing the InMemory impl feels a bit stupid

<br>

* Real Redis impl comming soon...<br>will be very important to test that...

* I want to know that *any* impl is correct

<br>
<div class="fragment" />

# LAWS!

---

### `RedisLaws`

* stateful:  A & B,  for n reps. forall laws
* actual laws
* A & B state comparison
* invariants from TLA+

<br>

*Show laws*

*Show RedisInMemoryTest <br> inMem(a) ~ inMem(b)*

---

Later added `RedisViaRedisson`

<pre><code class="lang-scala hljs" style="font-size:90%; margin-top:2em" data-trim data-noescape>
'left - {
  val t = new RedisLaws.Tester[IO](id, <span style="background:#080">redis</span>, id, <span style="background:#a0a">inmem</span>, evictSS, await)
  t.testAllLaws(reps)
}

'right - {
  val t = new RedisLaws.Tester[IO](id, <span style="background:#a0a">inmem</span>, id, <span style="background:#080">redis</span>, evictSS, await)
  t.testAllLaws(reps)
}
</code></pre>

---

## TLA+ &nbsp; ⇒ &nbsp; Code

<br>

* Scala
  * RedisAlgebra
    * RedisInMemory
    * RedisViaRedisson
* Redis
  * Lua functions

---

```tla
PublishEvents(events) ==
  pub' = pub \union (sub \X events)

```

<hr>

```scala

// publishEvents [channel] [event]*

val publishEvents = Lua {
  implicit val channel = Channel("c")
  s"""
     |${declareChannel(1)}
     |
     |for i = 2,#ARGV do
     |  ${publish.one("ARGV[i]")}
     |end
   """.stripMargin
}
```

---


```tla
PublishEvents(events) ==
  pub' = pub \union (sub \X events)
```

<hr>

```lua

-- publishEvents [channel] [event]*

local c = ARGV[1]

for i = 2,#ARGV do
  redis.call('publish',c,ARGV[i])
end
```

---

<pre><code class="lang-tla hljs" style="font-size:100%" data-trim data-noescape>
RedisWriteSnapshot(ver, eventsToPublish, OnOk, OnFail) ==

  /\ IF ver > redis.ver
     THEN
       /\ redis' = [ver    |-> ver,
                    events |-> {e \in redis.events : e > ver}]
       /\ OnOk
     ELSE
       /\ UNCHANGED redis
       /\ OnFail

  /\ PublishEvents(eventsToPublish)
</code></pre>

---

RedisWriteSnapshot in Lua

<pre><code class="lang-lua hljs" style="font-size:70%; line-height:1.2em" data-trim data-noescape>
local ks  = KEYS[1]
local ke  = KEYS[2]
local c   = ARGV[1]
local ver = tonumber(ARGV[2])
local bin = ARGV[3]

local ok = ver > (tonumber(redis.call('LINDEX',ks,0)) or 0)

if ok then
  redis.call('LPOP',ks)
  redis.call('LPOP',ks)
  redis.call('LPUSH',ks,bin,ver)
  redis.call('ZREMRANGEBYSCORE',ke,1,ver)
end

for i = 4,#ARGV do
  redis.call('publish',c,ARGV[i])
end

return ok
</code></pre>

---

<pre><code class="lang-tla hljs" style="font-size:85%" data-trim data-noescape>
RedisWriteEvents(eventsToCache, eventsToCacheAndPublish, OnOk, OnFail) ==
  LET events     == eventsToCache \union eventsToCacheAndPublish
      newEvents  == {e \in events : e > RedisTotalVer}
      fail       == /\ OnFail
                    /\ UNCHANGED redis
      apply      == /\ OnOk
                    /\ redis' = [redis EXCEPT !.events = @ \union newEvents]
  IN /\ IF newEvents = {} THEN
          fail
        ELSE IF Min[newEvents] > RedisTotalVer + 1 THEN
          fail \* Gaps in redis.events prohibited
        ELSE
          apply
     /\ PublishEvents(eventsToCacheAndPublish)
</code></pre>


---

😂 RedisWriteEvents in Lua 😆

<pre><code class="lang-lua hljs" style="font-size:50%; line-height:1.2em" data-trim data-noescape>
-- writeEvents [key] [key] [channel] ([cmd] [event data] …)

local ks = KEYS[1]
local ke = KEYS[2]
local c = ARGV[1]
local v = ((redis.call('EXISTS',ke)==0)
            or ((tonumber(redis.call('LINDEX',ks,0)) or 0) + 1 == tonumber(redis.call('ZRANGE',ke,0,0,'WITHSCORES')[2]))
          ) and (tonumber(redis.call('ZRANGE',ke,-1,-1,'WITHSCORES')[2]) or (tonumber(redis.call('LINDEX',ks,0)) or 0)) or 0

local n = 0
local s = 0
repeat
  n = n + 2
  s = tonumber(ARGV[n])
  if s ~= nil then
    s = math.abs(s)
  end
until s == nil or s > v

local ok = s == v + 1

if ok then
  local prev,j = v,0
  for i = n,#ARGV,2 do
    j = math.abs(tonumber(ARGV[i]))
    if j ~= (prev + 1) then break end
    redis.call('ZADD',ke,'NX',j,ARGV[i+1])
    prev=j
  end
end

for i = 2,#ARGV,2 do
  if tonumber(ARGV[i]) < 0 then
    redis.call('publish',c,ARGV[i+1])
  end
end

return ok
</code></pre>

---

ok lol enough of that

<br>

1. UpdateRequest
2. <span style="color:#f00">UpdateRespond</span>
3. RedisPublishEvent

---

<p class="stretch">
<a href=shipreq-algo.svg><img src=shipreq-algo.svg /></a>
</p>

---

In TLA+, each bubble in the diagram is a step

```tla
UpdateRespond ==
  \/ Update_ReadRedis
  \/ Update_ReadDb
  \/ Update_WriteRedis1
  \/ Update_WriteDb
  \/ Update_WriteRedis2
  \/ Update_Respond
```

---

The procedure has its own state (i.e. local variables)

<pre><code class="lang-tla hljs" style="font-size:75%" data-trim data-noescape>
VARIABLE procsU \* State of Update processors (i.e. threads in webapps)

TypeInvariants ==
  procsU \in SUBSET [
    req     : Request,
    status  : {"ReadRedis", "ReadDb", "WriteRedis1", "WriteDb", "WriteRedis2", "Respond"},
    user    : User,
    redisVer: Nat, \* The version of Redis at the last read from Redis
    ver     : Nat] \* The version of the Project in memory (0=none)
</code></pre>

---

<pre><code class="lang-tla hljs" style="font-size:78%" data-trim data-noescape>
req     : Request,
status  : {"ReadRedis", "ReadDb", "WriteRedis1", "WriteDb", "WriteRedis2", "Respond"},
user    : User,
redisVer: Nat, \&#42; The version of Redis at the last read from Redis
ver     : Nat] \&#42; The version of the Project in memory (0=none)
</code></pre>
<hr>
<table>
<tr><th>TLA+</th><th>Scala</th></tr>
<tr><td>req</td><td>Call stack</td></tr>
<tr><td>status</td><td>State.status</td></tr>
<tr><td>user</td><td>N/A</td></tr>
<tr><td>redisVer</td><td>State.redis</td></tr>
<tr><td>ver</td><td>State.local</td></tr>
</table>

---

<pre><code class="lang-tla hljs" style="font-size:78%" data-trim data-noescape>
req     : Request,
status  : {"ReadRedis", "ReadDb", "WriteRedis1", "WriteDb", "WriteRedis2", "Respond"},
user    : User,
redisVer: Nat, \* The version of Redis at the last read from Redis
ver     : Nat] \* The version of the Project in memory (0=none)
</code></pre>
<hr>
<pre><code class="lang-scala hljs" style="font-size:80%; line-height:1.2em" data-trim data-noescape>
final case class State(local : ProjectAndOrd,
                       redis : Redis.ProjectCache,
                       status: Status)

sealed trait Status
object Status {

  case object ReadRedis extends Status
  case object ReadDb    extends Status
  case object WriteDb   extends Status

  // These steps need more data / refinement. (Remember spec => impl)

  final case class WriteRedis1(newEvents: VerifiedEvent.Seq) extends Status

  final case class WriteRedis2(newProject: Project,
                               newEvent  : VerifiedEvent) extends Status
}
</code></pre>

---

That's the state, what about the steps?

<pre><code class="lang-tla hljs" style="font-size:90%; margin-top:2em" data-trim data-noescape>
Update_ReadRedis == \E p \in procsU :
  /\ p.status = "ReadRedis"

  /\ procsU' = Replace(procsU, p, [p EXCEPT
                !.ver      = RedisTotalVer,
                !.redisVer = RedisTotalVer,
                !.status   = IF RedisTotalVer > p.ver THEN "WriteDb"
                             ELSE "ReadDb"])
  
  /\ UNCHANGED << db, redis, pub, userState, procsL, procsR, procsS, sub >>
</code></pre>

<hr>
<pre><code class="lang-scala hljs" style="font-size:90%; line-height:1.2em" data-trim data-noescape>
case ReadRedis =>
  for {
    r     <- redis.read(pid)
    built <- r.build(pid)
  } yield built match {
    
    case \/-(p) => -\/(s.copy(local  = p,
                              redis  = r,
                              status = if (r.ord > s.local.ord) WriteDb
                                       else ReadDb))

    case -\/(e) => \/-(-\/(e))
  }
</code></pre>

---

<pre><code class="lang-tla hljs" style="font-size:90%; margin-top:2em" data-trim data-noescape>
Update_ReadDb == \E p \in procsU :
  /\ p.status = "ReadDb"

  /\ procsU' = Replace(procsU, p, [p EXCEPT
                 !.ver    = db.ver,
                 !.status = "WriteRedis1"])

  /\ UNCHANGED << db, redis, pub, userState, procsL, procsR, procsS, sub >>
</code></pre>

<hr>
<pre><code class="lang-scala hljs" style="font-size:85%" data-trim data-noescape>
case ReadDb =>
  for {
    cacheBuilt <- s.redis.buildNonEmpty(pid)
    p1          = s.local max cacheBuilt
    newEvents  <- runDB(db.getProjectEvents(pid, DB.EventFilter.given(p1.ord)))
    built      <- apEvent.append(pid, p1, newEvents)
  } yield built match {

    case \/-(p2) => -\/(s.copy(local  = p2,
                               status = WriteRedis1(newEvents)))

    case -\/(e)  => \/-(-\/(e))
  }
</code></pre>

---

blah blah blah followed by:

<pre><code class="lang-tla hljs" style="font-size:90%; margin-top:1em" data-trim data-noescape>
UpdateRespond ==
  \/ Update_ReadRedis
  \/ Update_ReadDb
  \/ Update_WriteRedis1
  \/ Update_WriteDb
  \/ Update_WriteRedis2
  \/ Update_Respond
</code></pre>

<hr>
<pre><code class="lang-scala hljs" style="font-size:75%; line-height:1.2em" data-trim data-noescape>
type Result = ErrorMsg \/ VerifiedEvent.Seq

def apply(pid: ProjectId, mkEvent: Project => MakeEvent.Result): F[Result] = {

  def loop(s: State): F[State \/ Result] = {
    val main: F[State \/ Result] = s.status match {
      case ReadRedis                         => ...
      case ReadDb                            => ...
      case WriteRedis1(newEvents)            => ...
      case WriteDb                           => ...
      case WriteRedis2(newProject, newEvent) => ...
    }
    trace.newSpan(s.status.name)(_ =>
      metrics.projectSpaWebSocketStep("update", s.status.name)(
        main))
  }

  F.tailrecM(loop)(initialState)
}
</code></pre>

---

…then finally all of this code gets tested as<br>thoroughly as you would test anything else,<br>TLA+ spec or no

---

<span style="font-size:50%">interesting but…</span>

# Can TLA+ GENERATE CODE? OR DATA / MODELS? OR TESTS? NOT TO WOULD MEAN DUPLICATION AND DISASTER.

---

## Could TLA+ generate...

<br>

* Scala data/models: <span style="color:#f88">no</span>
* Scala logic: <span style="color:#f88">no</span>
* Scala laws: <span style="color:#f88">no</span>
* Scala tests: <span style="color:#f88">no</span>
* Scala invariants: <span style="color:#f88">no</span>
* Lua code: <span style="color:#f88">no</span>
* SQL: <span style="color:#f88">no</span>

---

<pre><code class="lang-tla hljs" style="font-size:70%" data-trim data-noescape>
Update_ReadRedis == \E p \in procsU :
  /\ p.status = "ReadRedis"
  /\ procsU' = Replace(procsU, p, [p EXCEPT !.ver      = RedisTotalVer,
                                            !.redisVer = RedisTotalVer,
                                            !.status   = IF RedisTotalVer > p.ver THEN "WriteDb" ELSE "ReadDb"])
  /\ UNCHANGED << db, redis, pub, userState, procsL, procsR, procsS, sub >>
</code></pre>

This simple step involves:
* Scala: `case class State`
* Scala: `case class Status`
* Scala logic to apply events to a snapshot
* Scala error handling
* Redis algebra
* Redis Java library
* Redis impl
* A Redis Lua proc

---

Even the simplest TLA+ atom like:

<div style="font-family:monospace; font-size:50%; margin-bottom:2em; background:#000">
VARIABLE db <span style="color:#888">\\* Project version. Number of events.</span>
</div>

<div class="fragment" />
Ends up with this much Scala interface:

<pre><code class="lang-scala hljs" style="font-size:70%; line-height:1.2em" data-trim data-noescape>
def getProjectMetaData(id: ProjectId): F[Option[ProjectMetaData]]

def getProjectEvents(id: ProjectId, f: EventFilter): F[VerifiedEvent.Seq]

sealed trait EventFilter
object EventFilter {

  case object IncludeAll extends EventFilter
  final case class ExcludeUpTo(ord: EventOrd) extends EventFilter
  final case class Set(ords: NonEmptySet[EventOrd]) extends EventFilter

  def given(alreadyGot: Option[EventOrd.Latest]): EventFilter =
    alreadyGot match {
      case Some(ord) => ExcludeUpTo(ord)
      case None      => IncludeAll
    }
}

def saveProjectEvent(id: ProjectId, ord: EventOrd, event: ActiveEvent, hashes: HashRecs)
  : F[Throwable \/ VerifiedEvent]
</code></pre>

---

<span style="font-family:monospace; font-size:50%"><br>service 1: ---------------------> <br>service 2: ---------------------> <br>service 3: ---------------------> <br>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;time: ---------------------></span>

<br>

TLA+ = <span style="background:#f11">abstract</span> slices of <span style="background:#993;color:#000">time</span>, spanning all <span style="background:#33a">space</span>

Code = <span style="color:red; font-weight:bold">detailed</span> slice of <span style="background:#33a">space</span>, spanning all <span style="background:#993;color:#000">time</span>

---

Is TLA+ worth it considering the dev/test effort required once a spec is complete?

<br>

My opinion = Yes x100!