---- MODULE pizza__06 ----
EXTENDS Integers
VARIABLES ordering, ordered, told_coordinator, interfered
people == {"rincewind", "luggage", "twoflower"}
pizzas == {"double beech with extra oak", "hawaai with extra tuna", "rat-onna-stick"}
no_pizza == "No Pizza"
vars == <<ordering, ordered, told_coordinator, interfered>>
max_interfered == 3

Init == 
  /\ ordering = [p \in people |-> no_pizza]
  /\ ordered = [p \in people |-> no_pizza]
  /\ interfered = [p \in people |-> 0]
  /\ told_coordinator = {}

CalculateInterference(p) ==
    IF ordered[p] # ordering[p] THEN 
      IF interfered[p] + 1 >= max_interfered THEN
        max_interfered
      ELSE
        interfered[p] + 1
    ELSE 
      interfered[p]

Restart ==
    /\ told_coordinator = people
    /\ ordered' = [p \in people |-> no_pizza ]
    /\ ordering' = [p \in people |-> no_pizza ]
    /\ interfered' = [p \in people |-> CalculateInterference(p)]
    /\ told_coordinator' = {}

ChangeMind(person) ==
  /\ ordering[person] # no_pizza
  /\ \E pizza \in pizzas: 
    /\ pizza # ordering[person]
    /\ ordering' = [ordering EXCEPT ![person] = pizza]
  /\ UNCHANGED <<ordered, told_coordinator, interfered>>

DecideOnPizza(person) ==
  /\ ordering[person] = no_pizza
  /\ \E pizza \in pizzas:
      /\ ordering' = [ordering EXCEPT ![person] = pizza]
      /\ UNCHANGED <<ordered, told_coordinator, interfered>>

TellCoordinator(person) ==
  /\ person \notin told_coordinator
  /\ ordering[person] # no_pizza
  /\ ordered' = [ordered EXCEPT ![person] = ordering[person]]
  /\ told_coordinator' = told_coordinator \union {person}
  /\ UNCHANGED <<ordering, interfered>>

OrderCorrect(p) ==
  \/ interfered[p] = max_interfered
  \/ /\ interfered[p] < max_interfered 
    /\ ordering[p] = ordered[p] 
    /\ ordering[p] # no_pizza

EventuallyCorrect == <>(\A p \in people: OrderCorrect(p))

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
  /\ WF_vars(Restart)

InterferenceBounded ==
  \A p \in DOMAIN interfered: interfered[p] >= 0 /\ interfered[p] <= max_interfered

====