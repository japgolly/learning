type Request
val Requests: Set[Request]

type User
val Users: Set[User]


case class Db(ver: Int)

case class Redis(
  ver   : Int,
  events: Set[Int])

type Pub = (User, Int)

case class Proc(
  req     : Request,
  status  : "ReadRedis".type | "ReadDB".type | "WriteRedis1".type | "WriteDB".type | "WriteRedis2".type | "Done".type,
  user    : User,
  redisVer: Int,
  ver     : Int)

type UserState = User => UserStateValue

case class UserStateValue(
  online: Boolean,
  ver   : Int,
  future: Set[Int],
  reqs  : Seq[Request])



//  /\ \A u \in User :
//    LET s == userState[u]
//    IN /\ s.online => s.ver > 0
//       /\ s.ver <= db.ver
//       /\ \A e \in s.future : e > s.ver + 1

Users.forall { u =>
  val s = userState(u)
  (!s.online || s.ver > 0)
    && (s.ver <= db.ver)
    && s.future.forall(_ > s.ver + 1)
}


// ApplyEvents[v \in Nat, es \in SUBSET Nat] ==
//   LET n == v + 1
//   IN IF n \in es
//      THEN ApplyEvents[n, es \ {n}]
//      ELSE <<v,es>>

def applyEvents(v: Int, es: Set[Int]): (Int, Set[Int]) = {
  val n = v + 1
  if (es.contains(n))
    applyEvents(n, es - n)
  else
    (v, es)
}
