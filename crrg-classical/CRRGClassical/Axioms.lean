import CRRGClassical.Easier
import CRRGClassical.DMCheck
import CRRGClassical.RegionProgress
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
-- v0.12.0. Cancellation and a computed Dershowitz-Manna checker with proof-producing certificates
#print axioms dm_add_cancel
#print axioms dm_singleton_iff
#print axioms dm_aligned_singleton_iff
#print axioms dmCheck_sound_complete
#print axioms withComputedCert_credited_iff
-- v0.12.0. Credited labels stay at or below the root's label
#print axioms dmlt_le_some
#print axioms record_le_root
#print axioms credited_le_root
#print axioms top_root_credit
#print axioms creditOf_top_iff
-- v0.12.0. Stalls with steps where nothing changes; faithful lane logs; the gate model's lanes
#print axioms no_infinite_credits_stutter
#print axioms dichotomy
#print axioms faithful_newConflict_refuted
#print axioms lane_progress_unparks
#print axioms lane_projection_faithful
#print axioms gate_lane_dichotomy
-- v0.12.0. A finite region model (separate from the certified state)
#print axioms RegionProgress.root_iff_open
#print axioms RegionProgress.frontier_counterexample_refutes_root
#print axioms RegionProgress.split_close_bound
#print axioms RegionProgress.empty_root_zero_steps
#print axioms RegionProgress.split_weight_conserved
#print axioms RegionProgress.close_weight_decreases
