module alloy/rollup_scenarios

open alloy/rollup_data_model
open alloy/rollup_dynamics

/* SCENARIOS: SIMPLE ROLLUP */

/* Start with empty finalized state and no proofs; progress to 
multiple blocks.*/
pred rollup_process_test1 {
  no L1.proofs
  no L1.commitments
  eventually (#L1.finalized_state = 2)  
} 

run {
  spec_simple 
  rollup_process_test1
} for 7

run {
  spec_forced_queue
  rollup_process_test1
} for 7


/* Produce two different commitment/proof pairs 
   for the same state, finalize one [other is never finalized].*/
pred rollup_process_test2 {
    no proofs
    no commitments
    eventually (some c1 , c2 : Commitment 
    | c1.state = c2.state
    and eventually (c1.diff in L1.finalized_state.elems))
}   

run {
  spec_simple
  rollup_process_test2 
} for 7


/* Receive proof and commitment in different order. */
pred rollup_process_test3 {
  eventually (
    some p : Proof, c : Commitment | receive_proof[p]
    and after receive_commitment[c]
    and after after rollup_simple[c,p]
  )
}
run {
  spec_simple
  rollup_process_test3
} for 7


/* Receive commitment for longer state which gets later finalized. */
pred rollup_process_test4 {
  no L1.commitments
  no L1.proofs
  eventually (
    some c : Commitment, p : Proof | receive_commitment[c]
    and #c.state > #L1.finalized_state 
    and eventually (L1.finalized_state = c.state and after  
      rollup_simple[c,p])
  )
}

run {
  spec_simple
  rollup_process_test4
} for 10


/* sequence of events */
pred rollup_process_test5 {
  eventually (
  ReceiveComm in events
  ; ReceiveProof in events
  ; ProcessSimple in events
  ; ReceiveComm in events
  ; ProcessSimple in events
  ; ReceiveProof in events
  ; ProcessSimple in events
  )
}

run {
  spec_simple
  rollup_process_test5
} for 10

/* Number of elements in commitments > 1 and goes to 0 in one step 
   [only possible if deleted commitments were for the same state  
  as the one which was finalized] */
pred rollup_process_test6 {
  eventually (
    #L1.commitments > 1 ; #L1.commitments = 0
  )
}

run {
  spec_simple
  rollup_process_test6
} for 10


/* SCENARIOS: COLD ROLLUP (simple + forced_queue) */

/* Finalize long forced queue in one go. */
pred cold_rollup_test1 {
  eventually (
    #forced_queue = 3
    and eventually (#forced_queue = 3 and #forced_queue' = 0)
  )
}


run { 
  spec_simple
  cold_rollup_test1 
} for 7

/* finalize forced queue one element at a time */
pred cold_rollup_test2 {
  eventually (
      #forced_queue = 3
    ; #forced_queue = 2
    ; #forced_queue = 1
    ; #forced_queue = 0
  )
}

run { 
  spec_forced_queue
  cold_rollup_test2
} for 7


/* processes forced queue elements out of order */
pred cold_rollup_test3 {
  spec_blacklist_eager
  always (all x : Input | #tx.x < 2)
  eventually (
    some f1, f2 : ForcedInput | 
      L1.forced_queue.idxOf[f1] < L1.forced_queue.idxOf[f2] 
      and f1 in L1.forced_queue.elems
      and f2.tx not in all_finalized_inputs
      and f1.tx not in all_finalized_inputs
      and eventually(
          f2.tx in all_finalized_inputs and f1.tx not in all_finalized_inputs
        )
  )
}

run { 
  spec_forced_queue
  cold_rollup_test3
}

/* normally process proofs/commitments with forced queue being empty. */
pred cold_rollup_test4 {
  always (no L1.forced_queue.elems)
  eventually (
    #L1.finalized_state = 1
    ; #L1.finalized_state = 2
    ; #L1.finalized_state = 3
  )   
}

run { 
  spec_forced_queue
  cold_rollup_test4
} for 7

/* sequence of events */
pred cold_rollup_test5 {
  eventually (
  ReceiveComm in events[]
  ; ReceiveForced in events[]
  ; ReceiveProof in events[]
  ; ProcessSimple in events[]
  ; ReceiveComm in events[]
  )
}

run { 
  spec_forced_queue
  cold_rollup_test5
} for 7

/*  input appears in the middle of the `forced_queue` and jumps to the first head 
position in the next round */ 

pred cold_rollup_test6 {
  eventually {
    some f : ForcedInput | L1.forced_queue.idxOf[f] = 3 and L1.forced_queue'.idxOf[f] = 0
  }
} 

run { 
  spec_forced_queue
  cold_rollup_test6
} for 7
  

/* SCENARIOS: BLACKLISTs (simple + forced_queue + eager blacklists) */

/* start with non-blacklisted input which eventually gets blacklisted */
pred eager_blacklist_test1 {
  no L1.blacklist
  eventually(
    some x : Input |  
      x not in L1.blacklist 
  and eventually (x in L1.blacklist) 
  )
}

run { 
  spec_blacklist_eager
  eager_blacklist_test1
}


/* currently blacklisted input gets non-blacklisted */
pred eager_blacklist_test2 {
  no L1.blacklist
  eventually(
    some x : Input |  
      x in L1.blacklist 
  and eventually (x not in L1.blacklist) 
  )
}

run { 
  spec_blacklist_eager
  eager_blacklist_test2
}

/* currently blacklisted input gets in the forced queue */
pred eager_blacklist_test3 {
  no L1.blacklist
  eventually(
    some x : Input |  
      x in L1.blacklist 
  and eventually (x in L1.forced_queue.elems.tx) 
  )
} 

run { 
  spec_blacklist_eager
  eager_blacklist_test3
} for 7

/* currently blacklisted input gets finalized */
pred eager_blacklist_test4 {
 no L1.blacklist
 eventually(
    some x : Input |  
        x in L1.blacklist 
    and (x not in L1.finalized_state.elems.block_inputs.elems) 
  and eventually (x in L1.finalized_state.elems.block_inputs.elems) 
  )
} 

run { 
  spec_blacklist_eager
  eager_blacklist_test4
} for 7

/* non finalized input which is blacklisted by queued forced policy gets finalized */
pred eager_blacklist_test5 {
  eventually(
    some x : Input |  
      x in L1.forced_queue.elems.predicate
      and x not in all_finalized_inputs
      and eventually (x in all_finalized_inputs) 
  )
}

run { 
  spec_blacklist_eager
  eager_blacklist_test5
}


/* input is in the blacklist and is in the forced queue and 
  it gets finalized */
pred eager_blacklist_test6 {
  eventually(
    some x : Input |  
      x in L1.blacklist 
      and x in L1.forced_queue.elems.tx 
      and eventually (x in all_finalized_inputs) 
  )
}

run { 
  spec_blacklist_eager
  eager_blacklist_test6
}

/* forced input and blacklist in the forced queue and forced input
 is blacklisted by the new policy 
 in front of the policy [in this case forced input is always] */
pred eager_blacklist_test7 {
  eventually (
    some x : ForcedInput, p : ForcedBlacklistPolicy |
        x.tx  in p.predicate
        and x in L1.forced_queue.elems 
        and p in L1.forced_queue.elems
  )
}

run { 
  spec_blacklist_eager
  eager_blacklist_test7
}

/* upgrade finished then accept new forced queue */
pred soft_blacklist_test1 {
  L1.ongoing_upgrade = none
  and eventually (some L1.ongoing_upgrade
   and eventually (no L1.ongoing_upgrade) 
    and eventually (some L1.forced_queue))
}

run { 
  spec_blacklist_soft
  soft_blacklist_test1
}

/* inputs get queued upgrade phase */
pred soft_blacklist_test2 {
  L1.ongoing_upgrade = none
  no L1.blacklist
  and eventually (some L1.ongoing_upgrade
    and some L1.forced_queue
   and eventually (no L1.ongoing_upgrade and some L1.blacklist))
}

run { 
  spec_blacklist_soft
  soft_blacklist_test2
}

/* inputs get finalized during upgrade */
pred soft_blacklist_test3 {
  L1.ongoing_upgrade = none
  no L1.blacklist
  no L1.finalized_state

  and eventually (some L1.ongoing_upgrade
    and no L1.finalized_state 
      and eventually (some L1.finalized_state and some L1.ongoing_upgrade))
}

run { 
  spec_blacklist_soft
  soft_blacklist_test3
}

/* blacklisted element eventually gets finalized */
pred soft_blacklist_test4 {
  no L1.finalized_state
  some x : Input | x in L1.blacklist
    and eventually (x in all_finalized_inputs)
}

run { 
  spec_blacklist_soft
  soft_blacklist_test4
}