import CRRGCore

/-! Axiom report for the headline theorems and operations (captured in `BUILD.log`). -/

open CRRGCore

-- Basic: search narrowing, transitions, chains
#print axioms Frontier.replaceAt_transition
#print axioms Chain.closeRoot
#print axioms Frontier.dead_of_refuted
-- Easier: labels and the multiset lift
#print axioms Label.lt_wf
#print axioms Step.acc_append
#print axioms Step.wf
#print axioms labelStep_wf
#print axioms PermStep.wf
#print axioms DMLt.wf
#print axioms MechCert.settle
#print axioms Label.not_lt_top_top
#print axioms Label.not_lt_cross
#print axioms residual_sufficient
#print axioms Family.close_of_step
-- Guarded: composition, escapes, hidden debt, partitions
#print axioms GuardedMap.toSplit
#print axioms EscapeMap.toSplit
#print axioms GuardedEdge.toSplit
#print axioms guardedComp
#print axioms guardedComp_escapes
#print axioms hidden_debt_not_edge
#print axioms withEdgeLeaf
#print axioms rangeSplit
-- State: verify, commit or reject
#print axioms State.commit
#print axioms State.commit_transition
#print axioms State.commit_no_conflict
#print axioms State.creditOf_sound
#print axioms State.commit_credit_record
#print axioms State.commit_rootRefuted
#print axioms State.no_infinite_credits
#print axioms Move.closeByComputation
#print axioms State.easierSucc_wf
#print axioms State.refute
#print axioms State.learn
#print axioms State.rootRefuted_sound
#print axioms resolve_claims
-- Route
#print axioms CertRoute.closes
#print axioms CertRoute.refuted
