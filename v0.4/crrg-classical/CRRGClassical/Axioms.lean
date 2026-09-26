import CRRGClassical.Easier
import CRRGClassical.State
import CRRGClassical.Route
import CRRGClassical.Converse
import CRRGClassical.Stall
import CRRGClassical.Ledger

/-! Axiom report for the classical slice (classical axioms are allowed in this library). -/

open CRRGClassical

#print axioms Step.wf'
#print axioms permStep_iff_cutExpand
#print axioms dmlt_iff_transGen
#print axioms transGen_cutExpand_iff_isDM
#print axioms dmlt_iff_isDM
#print axioms DMLt.wf'
#print axioms no_infinite_credits
#print axioms core_credit_classical
#print axioms core_commit_classical
#print axioms core_no_infinite_credits_classical
#print axioms withCert_credited
#print axioms runner_credit_sound
#print axioms creditOf_sound_classical
#print axioms commit_credit_record_classical
#print axioms easierSucc_wf_classical
#print axioms recordRun_of_advance
#print axioms no_infinite_credits_state
#print axioms Region.admit_comm
#print axioms admit_pointwise'
#print axioms admit_members'
#print axioms admit_nondischarging'
#print axioms admit_exclusion'
#print axioms admit_monotone
#print axioms admit_comm
#print axioms admitAll_perm
#print axioms demo_orders_agree
#print axioms demo_any_order
#print axioms demo_x_after_two
#print axioms demo_x_closed
#print axioms demo_y_after
#print axioms CRRGClassical.CertRoute.closes
#print axioms CRRGClassical.commit_transition
#print axioms Converse.card_listAt_eq
#print axioms Converse.classCap_iff_listBound
#print axioms progress_unparks
#print axioms parked_last_dry
#print axioms eventually_parked
#print axioms unparked_needs_conflicts
#print axioms record_frontier_credit
#print axioms recordAll_state
#print axioms no_ingredient_refused
#print axioms admitted_cites_new
