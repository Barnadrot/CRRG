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
-- v0.12.0. Guarded: the n-ary chain; no child of a guarded composition can be dropped
#print axioms guardedChain
#print axioms guardedChain_two
#print axioms guardedComp_irredundant
#print axioms guardedChain_irredundant
-- v0.12.0. State along runs (steps where nothing changes included): learned conflicts persist
#print axioms State.initial_clean
#print axioms State.advance_conflicts
#print axioms State.advance_clean
#print axioms State.run_conflicts_mono
#print axioms State.run_clean
#print axioms State.run_no_readmission
#print axioms State.run_conflict_refuted
-- v0.12.0. State: a self-move is accepted without credit, forever (acceptance by commit only)
#print axioms State.selfMove_commit
#print axioms State.infinite_uncredited
-- v0.12.0. Arith: closed integer arithmetic by reflection (rung 2)
#print axioms Arith.Formula.check_iff
#print axioms Arith.Formula.mechCert
-- v0.12.0. Gate: a DESIGNED model of the gate (not the deployed gate or the runner)
#print axioms Gate.step_refines
#print axioms Gate.refines
#print axioms Gate.no_infinite_credits
#print axioms Gate.appended_event_sound
#print axioms Gate.run_journal_ok
#print axioms Gate.journal_ids_unique
#print axioms Gate.fair_extension
