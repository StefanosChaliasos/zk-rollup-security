module alloy/rollup_scenarios

open alloy/rollup_data_model
open alloy/rollup_dynamics

/* SCENARIOS: SIMPLE ROLLUP */

/* Start with empty finalized state and no proofs; progress to 
multiple blocks.*/
run rollup_process_test1 {
  spec_L1_blacklist_eager
  no L1.finalized_state
  no L1.commitments
  eventually (#L1.finalized_state = 3)
} for 7

/* Produce two different commitment/proof pairs 
   for the same state, finalize one [other is never finalized].*/
run rollup_process_test2 {
  spec_L1_blacklist_eager
  eventually (some c1 , c2 : Commitment 
    | c1.state = c2.state
    and eventually (c1.diff in L1.finalized_state.elems) )
} for 7


/* Receive proof and commitment in different order. */
run rollup_process_test3 {
  spec_L1_blacklist_eager
  eventually (
    some p : Proof, c : Commitment | receive_proof[p]
    and after receive_commitment[c]
    and after after rollup_simple[c,p,L1.blacklist]
  )
}

/* Receive commitment for longer state which gets later finalized. */
run rollup_process_test4 {
  spec_L1_blacklist_eager
  no L1.commitments
  no L1.proofs
  eventually (
    some c : Commitment, p : Proof | receive_commitment[c]
    and #c.state > #L1.finalized_state 
    and eventually (L1.finalized_state = c.state and after  
      rollup_simple[c,p,L1.blacklist])
  )
} for 10

/* sequence of events */
run {
  spec_L1_blacklist_eager
  eventually (
  ReceiveComm in events[L1.blacklist]
  ; ReceiveProof in events[L1.blacklist]
  ; ProcessSimple in events[L1.blacklist]
  ; ReceiveComm in events[L1.blacklist]
  ; ProcessSimple in events[L1.blacklist]
  ; ReceiveProof in events[L1.blacklist]
  ; ProcessSimple in events[L1.blacklist]
  )
} for 10

/* Number of elements in commitments > 1 and goes to 0 in one step 
   [only possible if deleted commitments were for the same state  
  as the one which was finalized] */
run {
  spec_L1_blacklist_eager
  eventually (
    #L1.commitments > 1 ; #L1.commitments = 0
  )
} for 10


/* SCENARIOS: COLD ROLLUP (simple + forced_queue) */

/* Finalize long forced queue in one go. */
run cold_rollup_test1 {
  spec_L1_blacklist_eager
  eventually (
    #forced_queue = 3
    and eventually (#forced_queue = 3 and #forced_queue' = 0)
  )
}

/* finalize forced queue one element at a time */
run cold_rollup_test2 {
  spec_L1_blacklist_eager
  eventually (
      #forced_queue = 3
    ; #forced_queue = 2
    ; #forced_queue = 1
    ; #forced_queue = 0
  )
} for 5

/* processes forced queue elements out of order */
run cold_rollup_test3 {
  spec_L1_blacklist_eager
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

/* normally process proofs/commitments with forced queue being empty. */
run cold_rollup_test4 {
  spec_L1_blacklist_eager
  always (no L1.forced_queue.elems)
  eventually (
    #L1.finalized_state = 1
    ; #L1.finalized_state = 2
    ; #L1.finalized_state = 3
  )   
} for 7

/* sequence of events */
run cold_rollup_test5 {
  spec_L1_blacklist_eager
  always no ForcedBlacklistPolicy
  eventually (
  ReceiveComm in events[L1.blacklist]
  ; ReceiveForced in events[L1.blacklist]
  ; ReceiveProof in events[L1.blacklist]
  ; ProcessSimple in events[L1.blacklist]
  ; ReceiveComm in events[L1.blacklist]
  ; ProcessSimple in events[L1.blacklist]
  )
} for 7

/*  input appears in the middle of the `forced_queue` and jumps to the first head 
position in the next round */ 
run cold_rollup_test6 {
  spec_L1_blacklist_eager
  eventually {
    some f : ForcedInput | L1.forced_queue.idxOf[f] = 3 and L1.forced_queue'.idxOf[f] = 0
  }
} for 7
  

/* SCENARIOS: BLACKLISTs (simple + forced_queue + eager blacklists) */

/* start with non-blacklisted input which eventually gets blacklisted */
run eager_blacklist_test1 {
 spec_L1_blacklist_eager
  eventually(
    some x : Input |  
      x not in L1.blacklist 
  and eventually (x in L1.blacklist) 
  )
}

/* currently blacklisted input gets non-blacklisted */
run eager_blacklist_test2 {
 spec_L1_blacklist_eager
 no L1.blacklist
  eventually(
    some x : Input |  
      x in L1.blacklist 
  and eventually (x not in L1.blacklist) 
  )
}

/* currently blacklisted input gets in the forced queue */
run eager_blacklist_test3 {
 spec_L1_blacklist_eager
 no L1.blacklist
 eventually(
    some x : Input |  
      x in L1.blacklist 
  and eventually (x in L1.forced_queue.elems.tx) 
  )
} for 7

/* currently blacklisted input gets finalized */
run eager_blacklist_test4 {
 spec_L1_blacklist_eager
 no L1.blacklist
 eventually(
    some x : Input |  
        x in L1.blacklist 
    and (x not in L1.finalized_state.elems.block_inputs.elems) 
  and eventually (x in L1.finalized_state.elems.block_inputs.elems) 
  )
} for 7


/* non finalized input which is blacklisted by queued forced policy gets finalized */
run eager_blacklist_test5 {
 spec_L1_blacklist_eager
  eventually(
    some x : Input |  
      x in L1.forced_queue.elems.predicate
  and x not in all_finalized_inputs
  and eventually (x in all_finalized_inputs) 
  )
}


/* input is in the blacklist and is in the forced queue and 
  it gets finalized */
run eager_blacklist_test6 {
 spec_L1_blacklist_eager
  eventually(
    some x : Input |  
      x in L1.blacklist 
  and x in L1.forced_queue.elems.tx 
  and eventually (x in all_finalized_inputs) 
  )
}

/* forced input and blacklist in the forced queue and forced input
 is blacklisted by the new policy 
 in front of the policy [in this case forced input is always] */
run eager_blacklist_test7 {
  spec_L1_blacklist_eager
  eventually (
    some x : ForcedInput, p : ForcedBlacklistPolicy |
        x.tx  in p.predicate
        and x in L1.forced_queue.elems 
        and p in L1.forced_queue.elems
  )
}
