------------------------------------------------- MODULE shipreq_users -------------------------------------------------

EXTENDS FiniteSets, TLC

CONSTANT User

ASSUME IsFiniteSet(User)

VARIABLES userStates

TypeInvariants ==
  userStates \in [User -> [online: BOOLEAN]]

OfflineUser ==
  [online |-> FALSE]

Init ==
  userStates = [u \in User |-> OfflineUser]

------------------------------------------------------------------------------------------------------------------------

UserConnect ==
  \E u \in User :
    /\ ~userStates[u].online
    /\ userStates' = [userStates EXCEPT ![u].online = TRUE]

UserDisconnect ==
  \E u \in User :
    /\ userStates[u].online
    /\ userStates' = [userStates EXCEPT ![u] = OfflineUser]

Action ==
  \/ UserConnect
  \/ UserDisconnect

------------------------------------------------------------------------------------------------------------------------

ModelSymmetry == Permutations(User)

Spec == Init /\ [][Action]_userStates

THEOREM  Spec => []TypeInvariants

========================================================================================================================
