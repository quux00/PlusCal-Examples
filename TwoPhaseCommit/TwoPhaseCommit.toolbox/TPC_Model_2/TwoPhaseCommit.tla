--------------------- MODULE TwoPhaseCommit ----------------------
EXTENDS Naturals, TLC
(*
--algorithm TwoPhaseCommit {
  variables 
    managers = {"bob", "chuck", "dave"};
    restaurant_stage = [mgr \in managers |-> "start"];
    
  macro SetAll(state, kmgrs) {
    while (kmgrs # {}) {
        with (km \in kmgrs) {
           restaurant_stage[km] := state;
           kmgrs := kmgrs \ {km};
       };
    };
  }
    
  process (Restaurant \in managers)
  {
    c0: await restaurant_stage[self] = "propose";
    
        either {
          restaurant_stage[self] := "accept";
        } or {
          restaurant_stage[self] := "refuse";    
        };
    
    c1: await (restaurant_stage[self] = "commit") \/
              (restaurant_stage[self] = "abort");
    
        if (restaurant_stage[self] = "commit") {
          restaurant_stage[self] := "committed";
        } else {
          restaurant_stage[self] := "aborted";          
        };        
  }; \* end Restaurant process block

  process (Controller = "alice")
    variables rstMgrs, aborted = FALSE;    
  {  
    n0: rstMgrs := managers;
    n1: SetAll("propose", rstMgrs);
    n2: rstMgrs := managers;  \* reassign, since SetAll modified the original rstMgrs set
    n3: while (rstMgrs # {}) {
          with (r \in rstMgrs) {
            await (restaurant_stage[r] = "accept") \/ (restaurant_stage[r] = "refuse");
            if (restaurant_stage[r] = "refuse") {
              aborted := TRUE;
            };
            rstMgrs := rstMgrs \ {r};
          };
        };
        rstMgrs := managers;
        if (aborted = TRUE) {
    n4:   SetAll("abort", rstMgrs);
        } else {
    n5:   SetAll("commit", rstMgrs);
        };
  } \* end Controller process block

} \* end algorithm
*)    
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES managers, restaurant_stage, pc, rstMgrs, aborted

vars == << managers, restaurant_stage, pc, rstMgrs, aborted >>

ProcSet == (managers) \cup {"alice"}

Init == (* Global variables *)
        /\ managers = {"bob", "chuck", "dave"}
        /\ restaurant_stage = [mgr \in managers |-> "start"]
        (* Process Controller *)
        /\ rstMgrs = defaultInitValue
        /\ aborted = FALSE
        /\ pc = [self \in ProcSet |-> CASE self \in managers -> "c0"
                                        [] self = "alice" -> "n0"]

c0(self) == /\ pc[self] = "c0"
            /\ restaurant_stage[self] = "propose"
            /\ \/ /\ restaurant_stage' = [restaurant_stage EXCEPT ![self] = "accept"]
               \/ /\ restaurant_stage' = [restaurant_stage EXCEPT ![self] = "refuse"]
            /\ pc' = [pc EXCEPT ![self] = "c1"]
            /\ UNCHANGED << managers, rstMgrs, aborted >>

c1(self) == /\ pc[self] = "c1"
            /\ (restaurant_stage[self] = "commit") \/
               (restaurant_stage[self] = "abort")
            /\ IF restaurant_stage[self] = "commit"
                  THEN /\ restaurant_stage' = [restaurant_stage EXCEPT ![self] = "committed"]
                  ELSE /\ restaurant_stage' = [restaurant_stage EXCEPT ![self] = "aborted"]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << managers, rstMgrs, aborted >>

Restaurant(self) == c0(self) \/ c1(self)

n0 == /\ pc["alice"] = "n0"
      /\ rstMgrs' = managers
      /\ pc' = [pc EXCEPT !["alice"] = "n1"]
      /\ UNCHANGED << managers, restaurant_stage, aborted >>

n1 == /\ pc["alice"] = "n1"
      /\ IF rstMgrs # {}
            THEN /\ \E km \in rstMgrs:
                      /\ restaurant_stage' = [restaurant_stage EXCEPT ![km] = "propose"]
                      /\ rstMgrs' = rstMgrs \ {km}
                 /\ pc' = [pc EXCEPT !["alice"] = "n1"]
            ELSE /\ pc' = [pc EXCEPT !["alice"] = "n2"]
                 /\ UNCHANGED << restaurant_stage, rstMgrs >>
      /\ UNCHANGED << managers, aborted >>

n2 == /\ pc["alice"] = "n2"
      /\ rstMgrs' = managers
      /\ pc' = [pc EXCEPT !["alice"] = "n3"]
      /\ UNCHANGED << managers, restaurant_stage, aborted >>

n3 == /\ pc["alice"] = "n3"
      /\ IF rstMgrs # {}
            THEN /\ \E r \in rstMgrs:
                      /\ (restaurant_stage[r] = "accept") \/ (restaurant_stage[r] = "refuse")
                      /\ IF restaurant_stage[r] = "refuse"
                            THEN /\ aborted' = TRUE
                            ELSE /\ TRUE
                                 /\ UNCHANGED aborted
                      /\ rstMgrs' = rstMgrs \ {r}
                 /\ pc' = [pc EXCEPT !["alice"] = "n3"]
            ELSE /\ rstMgrs' = managers
                 /\ IF aborted = TRUE
                       THEN /\ pc' = [pc EXCEPT !["alice"] = "n4"]
                       ELSE /\ pc' = [pc EXCEPT !["alice"] = "n5"]
                 /\ UNCHANGED aborted
      /\ UNCHANGED << managers, restaurant_stage >>

n4 == /\ pc["alice"] = "n4"
      /\ IF rstMgrs # {}
            THEN /\ \E km \in rstMgrs:
                      /\ restaurant_stage' = [restaurant_stage EXCEPT ![km] = "abort"]
                      /\ rstMgrs' = rstMgrs \ {km}
                 /\ pc' = [pc EXCEPT !["alice"] = "n4"]
            ELSE /\ pc' = [pc EXCEPT !["alice"] = "Done"]
                 /\ UNCHANGED << restaurant_stage, rstMgrs >>
      /\ UNCHANGED << managers, aborted >>

n5 == /\ pc["alice"] = "n5"
      /\ IF rstMgrs # {}
            THEN /\ \E km \in rstMgrs:
                      /\ restaurant_stage' = [restaurant_stage EXCEPT ![km] = "commit"]
                      /\ rstMgrs' = rstMgrs \ {km}
                 /\ pc' = [pc EXCEPT !["alice"] = "n5"]
            ELSE /\ pc' = [pc EXCEPT !["alice"] = "Done"]
                 /\ UNCHANGED << restaurant_stage, rstMgrs >>
      /\ UNCHANGED << managers, aborted >>

Controller == n0 \/ n1 \/ n2 \/ n3 \/ n4 \/ n5

Next == Controller
           \/ (\E self \in managers: Restaurant(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

StateOK == /\ (\A i \in managers: restaurant_stage[i] \in {"start", "propose", "accept", "commit", "abort", "committed", "aborted", "refuse"})

Committed == /\ \/ <>(\A i \in managers: restaurant_stage[i] = "committed")
                \/ <>(\A i \in managers: restaurant_stage[i] = "aborted")

==================================================================
