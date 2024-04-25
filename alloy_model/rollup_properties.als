module alloy/rollup_properties

open alloy/rollup_data_model
open alloy/rollup_dynamics



check at_most_one_event {
  spec_no_censorship implies always lone events[none]
  spec_L1_blacklist_eager  implies always lone events[L1.blacklist]
} for 5


// if something gets into finilized_state then at some moment 
// there was a proof and a commitment for it
assert rollup_process_prop1 { 
 spec_L1_blacklist_eager implies
 always(
   all b : Block | some L1.finalized_state.idxOf[b]
     implies
      (once some c : Commitment, p : Proof |
         c in L1.commitments
     and p in L1.proofs
     and c.diff = p.diff
     and b = c.diff)
 )
}
check rollup_process_prop1 for 5

// final state grows monotonically
assert rollup_process_prop2 { 
  spec_L1_blacklist_eager implies always (finalized_state in finalized_state')
}
check rollup_process_prop2 for 5

// if forced_queue is non-empty and something was added to the finalized-state
// then the head of the forced queue was processed
assert cold_rollup_prop1 {
 spec_L1_blacklist_eager implies
  always (
   (some L1.forced_queue and some (L1.finalized_state' - L1.finalized_state))
     implies
         //some L1.finalized_state'.elems.block_inputs.idxOf[L1.forced_queue.first]
         L1.forced_queue.first.tx in new_finalized_inputs
  )
}
check cold_rollup_prop1 for 5

// if finalized state didn't change then forced_queue only increased
assert cold_rollup_prop2 {
 spec_L1_blacklist_eager implies
  always (
   (L1.finalized_state = L1.finalized_state')
     implies
       ForcedInput :> L1.forced_queue.elems in ForcedInput :> L1.forced_queue'.elems
  )
}
check cold_rollup_prop2 for 5

// if queue is not empty and didn't change then finalized_state didn' change
assert cold_rollup_prop3 {
 spec_L1_blacklist_eager implies
  always (
   (L1.forced_queue' = L1.forced_queue and some L1.forced_queue)
     implies
       L1.finalized_state = L1.finalized_state'
  )
}
check cold_rollup_prop3 for 5

// forced txs which were not processed move down in the forced queue
assert cold_rollup_prop4 {
 spec_L1_blacklist_eager implies
 always (
    (some L1.forced_queue 
    and #L1.finalized_state < #L1.finalized_state') implies
    (all x : ForcedEvent |
      (some L1.forced_queue.idxOf[x]
      and some L1.forced_queue'.idxOf[x])
       implies 
        L1.forced_queue'.idxOf[x] < L1.forced_queue.idxOf[x])
 )
}
check cold_rollup_prop4 for 5

// if something was in the forced queue and then disappeared from it then
// it was finalized
assert cold_rollup_prop5 {
  spec_L1_blacklist_eager implies
  always (
    all fi : ForcedInput | fi in L1.forced_queue.elems 
      implies always(fi not in L1.forced_queue.elems implies fi.tx in all_finalized_inputs)
  )
}
check cold_rollup_prop5 for 5

assert cold_rollup_prop6 {
  spec_L1_blacklist_eager implies
  always (
    some L1.forced_queue.elems implies  
       some L1.forced_queue.subseq[0,0]
  )
}
check cold_rollup_prop6 for 5

assert cold_rollup_prop7 {
  spec_L1_blacklist_eager implies
  always (
    all fi : ForcedInput, c : Commitment, p : Proof| 
       fi in L1.forced_queue.elems 
       and rollup_simple[c,p,L1.blacklist]  
       and fi.tx in c.diff.block_inputs.elems
      implies
        fi not in L1.forced_queue'.elems
  )
}
check cold_rollup_prop7 for 5


// blacklisted things do not get finanlized
pred blacklist_prop1 {
  always(
    all x : Input | 
       x in L1.finalized_state'.elems.block_inputs.elems 
   and x not in L1.finalized_state.elems.block_inputs.elems
          implies x not in L1.blacklist
  )
}
check {
  spec_L1_blacklist_eager implies blacklist_prop1
  spec_L1_blacklist_soft implies blacklist_prop1
 } for 5

// if something censored is in the head of the forced_queue 
// then finalized state will never change
pred blacklist_prop2 {
    always (
    all x : Input | (x in L1.blacklist and x = L1.forced_queue.first.tx)
        implies always (L1.finalized_state = L1.finalized_state')
  )
}
check {
  spec_L1_blacklist_eager implies blacklist_prop2 
  spec_L1_blacklist_soft implies blacklist_prop2 
} for 5

// forced input can be processed if it is not censored
assert blacklist_prop3 {
  spec_no_censorship implies
   always(
     all f : ForcedInput | receive_forced[f,L1.blacklist] implies 
       always (all c : Commitment, p : Proof 
                | c.diff.block_inputs.elems = f.tx 
                    and rollup_simple[c,p,none] 
                    and f.tx not in all_finalized_inputs
                      implies rollup_simple[c,p,L1.blacklist])
   )
}
check blacklist_prop3 for 5

// forced input can be added if it is not censored
assert blacklist_prop4 {
   always(
     all f : ForcedInput | receive_forced_broken[f,none] 
          and f.tx not in L1.blacklist
          and f.tx not in L1.forced_queue.elems.predicate
         implies receive_forced[f,L1.blacklist])
}
check blacklist_prop4 for 5

// if univ is censored then no new inputs are ever finalized
assert blacklist_prop5 {
  spec_all_censored implies always (no new_finalized_inputs)
}
check blacklist_prop5 for 5

//blacklisted can never appear in the head position of the queue
pred blacklist_prop6 {
 always (
    all x : Input | 
        not (x in L1.blacklist and x = L1.forced_queue.first.tx) 
  )
}
check {
  spec_L1_blacklist_eager implies blacklist_prop6
  spec_L1_blacklist_soft implies blacklist_prop6

 } for 5

// all inputs which stand behind new blacklist policy are not blacklisted
assert blacklist_prop7 {
    spec_L1_blacklist_eager implies  always (
      all x : ForcedBlacklistPolicy, y : ForcedInput |
         x in L1.forced_queue.elems
         and y in L1.forced_queue.elems
        and L1.forced_queue.idxOf[x] < L1.forced_queue.idxOf[y]
        implies y.tx not in x.predicate
    )
}
check blacklist_prop7 for 5



