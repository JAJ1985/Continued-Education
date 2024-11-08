---- MODULE pizza__03 ----
VARIABLES ordering, ordered, mind_changed, told_coordinator
people == {"rincewind", "luggage", "twoflower"}
pizzas == {"double beech with extra oak", "hawaai with extra tuna", "rat-onna-stick"}
no_pizza == "No Pizza"

Init == 
  /\ ordering = [p \in people |-> no_pizza]
  /\ ordered = [p \in people |-> no_pizza]
  /\ mind_changed = {}
  /\ told_coordinator = {}

Restart ==
    /\ told_coordinator = people
    /\ ordering # ordered
    /\ ordered' = [p \in people |-> no_pizza ]
    /\ told_coordinator' = {}
    /\ UNCHANGED <<ordering, mind_changed>>

ChangeMind(person) ==
  /\ ordering[person] # no_pizza
  /\ person \notin mind_changed
  /\ \E pizza \in pizzas: 
    /\ pizza # ordering[person]
    /\ ordering' = [ordering EXCEPT ![person] = pizza]
  /\ mind_changed' = mind_changed \union {person}
  /\ UNCHANGED <<ordered, told_coordinator>>

DecideOnPizza(person) ==
  /\ ordering[person] = no_pizza
  /\ \E pizza \in pizzas:
      /\ ordering' = [ordering EXCEPT ![person] = pizza]
      /\ UNCHANGED <<ordered, mind_changed, told_coordinator>>

TellCoordinator(person) ==
  /\ person \notin told_coordinator
  /\ ordering[person] # no_pizza
  /\ ordered' = [ordered EXCEPT ![person] = ordering[person]]
  /\ told_coordinator' = told_coordinator \union {person}
  /\ UNCHANGED <<ordering, mind_changed>>

ConfirmPerson(p) ==
  /\ ordered[p] = ordering[p]

ConfirmAll ==
  /\ \A p \in people:
    /\ ordered[p] # no_pizza
    /\ ConfirmPerson(p)
  /\ UNCHANGED <<ordering, ordered, mind_changed, told_coordinator>>

Next ==
  \/ \E person \in people:
      \/ DecideOnPizza(person)
      \/ TellCoordinator(person)
      \/ ChangeMind(person)
  \/ ConfirmAll
  \/ Restart

Spec == Init /\ [][Next]_<<ordering, ordered, mind_changed, told_coordinator>>
====