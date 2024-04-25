module alloy/rollup_soft_blacklist_properties

open alloy/rollup_data_model
open alloy/rollup_dynamics


pred upgradeability_events_transitions {
  always(
    not upgrade_in_progress implies
       after (not upgrade_in_progress or upgrade_queueing)
          and after 
            (not (upgrade_queueing_finished or upgrade_forced_queue_processing 
               or upgrade_forced_queue_processing_finished))
  )

  always(
    upgrade_queueing and some L1.forced_queue implies
       after (upgrade_queueing or upgrade_forced_queue_processing)
    and after (not (
        upgrade_forced_queue_processing_finished
        or (not upgrade_in_progress)
    ))
  )
  always(
  upgrade_queueing and no L1.forced_queue implies
     after (upgrade_queueing or upgrade_queueing_finished)
  )
  always(
  upgrade_forced_queue_processing and no L1.forced_queue implies
     after (upgrade_forced_queue_processing or upgrade_forced_queue_processing_finished)
  )
  always(
   upgrade_forced_queue_processing_finished implies 
     after (upgrade_forced_queue_processing_finished or not upgrade_in_progress)

  )
 
}

assert transitions_correct {
  spec_L1_blacklist_soft implies upgradeability_events_transitions
  
}
check transitions_correct


assert forced_queue_is_respected {
  spec_L1_blacklist_soft implies
  always (
    all x : Input | x in L1.forced_queue.elems.tx implies
       always (
        (upgrade_in_progress and after not upgrade_in_progress)
          implies (x in L1.finalized_state.elems.block_inputs.elems)
       )
  )
}
check forced_queue_is_respected



/*
General properties:
- State machine description:
    - no upgrade_in_progress can only go to queueing
    - queueing can only go to queue processing if queue is not empty
    or to processing finished if queue is empty
    - processing can only go to processing finished
    - processing finished can only go to not upgrade_in_progress
- If x in forced_queue and later upgrade finished then x is finalized
- if x is blacklisted but got finalized then there was blacklist update
- 

*/

run {
  spec_L1_blacklist_soft
  eventually (upgrade_in_progress 
              ; upgrade_queueing 
              ; upgrade_queueing_finished 
              ; upgrade_forced_queue_processing
              ; upgrade_forced_queue_processing_finished
              ; not upgrade_in_progress
              )
} for 15 steps

run {
  spec_L1_blacklist_soft
  eventually (
    upgrade_in_progress
    ; some x : Input | x in L1.forced_queue.elems.tx 
    and x not in all_finalized_inputs
    and x in L1.ongoing_upgrade.blacklist_policy.predicate
    and eventually (x in all_finalized_inputs and not upgrade_in_progress) 
  )
}