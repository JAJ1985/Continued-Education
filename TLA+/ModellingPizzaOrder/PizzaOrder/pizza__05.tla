---- MODULE pizza__05 ----
VARIABLES ordering, ordered, mind_changed, told_coordinator
people == {"rincewind", "luggage", "twoflower"}
pizzas == {"double beech with extra oak", "hawaai with extra tuna", "rat-onna-stick"}
no_pizza == "No Pizza"
vars == <<ordering, ordered, mind_changed, told_coordinator>>

Init == 
  /\ ordering = [p \in people |-> no_pizza]
  /\ ordered = [p \in people |-> no_pizza]
  /\ mind_changed = {}
  /\ told_coordinator = {}

Restart ==
    /\ told_coordinator = people
    /\ ordered' = [p \in people |-> no_pizza ]
    /\ ordering' = [p \in people |-> no_pizza ]
    /\ told_coordinator' = {}
    /\ mind_changed' = {}

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

OrderCorrect ==
  /\ \A p \in people:
    /\ ordered[p] # no_pizza
    /\ ordered[p] = ordering[p]

EventuallyCorrect ==
  /\ <>(OrderCorrect)

Next ==
  \/ \E person \in people:
      \/ DecideOnPizza(person)
      \/ TellCoordinator(person)
      \/ ChangeMind(person)
  \/ Restart

Spec == 
  /\ Init 
  /\ [][Next]_vars
  /\ \A p \in people: 
    /\ WF_vars(DecideOnPizza(p))
    /\ WF_vars(TellCoordinator(p))

====