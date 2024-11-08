ck---- MODULE pizza__01 ----
VARIABLES ordering, ordered
people == {"rincewind", "luggage", "twoflower"}
pizzas == {"double beech with extra oak", "hawaai with extra tuna", "rat-onna-stick"}
no_pizza == "No Pizza"

Init == 
  /\ ordering = [p \in people |-> no_pizza]
  /\ ordered = [p \in people |-> no_pizza]

DecideOnPizza(person) ==
  /\ ordering[person] = no_pizza
  /\ \E pizza \in pizzas:
      /\ ordering' = [ordering EXCEPT ![person] = pizza]
      /\ UNCHANGED ordered

TellCoordinator(person) ==
  /\ ordering[person] # no_pizza
  /\ ordered' = [ordered EXCEPT ![person] = ordering[person]]
  /\ UNCHANGED ordering

ConfirmPerson(p) ==
  /\ ordered[p] = ordering[p]

ConfirmAll ==
  /\ \A p \in people:
    /\ ordered[p] # no_pizza
    /\ ConfirmPerson(p)
  /\ UNCHANGED <<ordering, ordered>>

Next ==
  \/ \E person \in people:
      \/ DecideOnPizza(person)
      \/ TellCoordinator(person)
  \/ ConfirmAll

Spec == Init /\ [][Next]_<<ordering, ordered>>
====+