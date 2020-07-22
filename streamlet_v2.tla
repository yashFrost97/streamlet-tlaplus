---------------------------- MODULE streamlet_v2 ----------------------------
EXTENDS Sequences, Integers, Naturals, TLC, FiniteSets

CONSTANTS MAXEPOCHS, N
Nodes == 1..N

(*
--algorithm streamlet{
    variable votes = {}, proposal={},
    notarized = [ep \in 0..MAXEPOCHS |-> FALSE];
    
    define{
        NoOfVotes(ep, vo) == {response \in votes: response.epoch = ep /\ response.vote = vo}
    }
    
    macro Propose(ep, n){
        proposal := proposal \union {[epoch |-> ep, node |-> n]}
    }
    
    macro Vote(ep, n, v){
        votes := votes \union {[epoch |-> ep, node |-> n, vote |-> v]}
    }
    
    fair process(p \in Nodes)
    variable epoch = 0;
    {
    BEGIN:  while(epoch < MAXEPOCHS){
                
                if(epoch % N = self){
                    Propose(epoch, self);
                } else {
                    either {
                        Vote(epoch, self, 0);
                    }
                    or {
                        Vote(epoch, self, 1);
                    }
               
                };
                 if(Cardinality(NoOfVotes(epoch, 1)) \geq N \div 2){
                    notarized[epoch] := TRUE;
                
                };
                epoch := epoch +1; 
          }
        }
    }
}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-caecee1d3d65b25ffe67f14160c1ad35
VARIABLES votes, proposal, notarized, pc

(* define statement *)
NoOfVotes(ep, vo) == {response \in votes: response.epoch = ep /\ response.vote = vo}

VARIABLE epoch

vars == << votes, proposal, notarized, pc, epoch >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ votes = {}
        /\ proposal = {}
        /\ notarized = [ep \in 0..MAXEPOCHS |-> FALSE]
        (* Process p *)
        /\ epoch = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> "BEGIN"]

BEGIN(self) == /\ pc[self] = "BEGIN"
               /\ IF epoch[self] < MAXEPOCHS
                     THEN /\ IF epoch[self] % N = self
                                THEN /\ proposal' = (proposal \union {[epoch |-> epoch[self], node |-> self]})
                                     /\ votes' = votes
                                ELSE /\ \/ /\ votes' = (votes \union {[epoch |-> epoch[self], node |-> self, vote |-> 0]})
                                        \/ /\ votes' = (votes \union {[epoch |-> epoch[self], node |-> self, vote |-> 1]})
                                     /\ UNCHANGED proposal
                          /\ IF Cardinality(NoOfVotes(epoch[self], 1)) \geq N \div 2
                                THEN /\ notarized' = [notarized EXCEPT ![epoch[self]] = TRUE]
                                ELSE /\ TRUE
                                     /\ UNCHANGED notarized
                          /\ epoch' = [epoch EXCEPT ![self] = epoch[self] +1]
                          /\ pc' = [pc EXCEPT ![self] = "BEGIN"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ UNCHANGED << votes, proposal, notarized, epoch >>

p(self) == BEGIN(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-700a4e898d8b424b9e677b13eefcca77


=============================================================================
\* Modification History
\* Last modified Tue Jul 21 10:03:10 EDT 2020 by yashf
\* Created Tue Jul 21 10:02:46 EDT 2020 by yashf
