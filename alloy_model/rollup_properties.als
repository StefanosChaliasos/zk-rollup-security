module alloy/rollup_properties

open alloy/rollup_data_model
open alloy/rollup_dynamics


/* at most one event happens at a time */
check rollup_prop1 {
  spec_no_censorship implies always lone events
  spec_L1_blacklist_eager  implies always lone events
  spec_L1_blacklist_soft  implies always lone events
} for 5


/* if something gets into finilized_state then at some moment 
 there was a proof and a commitment for it which corresponded to the
 current state */
pred rollup_process_prop2 { 
 always(
   all b : Block | some L1.finalized_state.idxOf[b]
     implies
      (once some c : Commitment, p : Proof |
         c in L1.commitments
     and p in L1.proofs
     and c.diff = p.diff
     and b = c.diff
     and c.state = L1.finalized_state)
 )
}
check {
  spec_L1_blacklist_eager implies rollup_process_prop2
  spec_L1_blacklist_soft implies rollup_process_prop2
} for 5


/* final state grows monotonically */
pred rollup_process_prop3 { 
  always (finalized_state in finalized_state')
}
check {
  spec_L1_blacklist_eager implies rollup_process_prop3
  spec_L1_blacklist_soft implies rollup_process_prop3
} for 5

/*
The commitment/proof which is smaller than current state never 
gets successfully processed.
*/
pred rollup_process_prop4 { 
 always(
   all c : Commitment, p : Proof | 
      #c.state < #L1.finalized_state
     implies
      not (rollup_simple[c,p])
 )
}
check {
  spec_L1_blacklist_eager implies rollup_process_prop4
  spec_L1_blacklist_soft implies rollup_process_prop4
} for 5




/* if forced_queue is non-empty and something was added to the finalized-state
   then the head of the forced queue was processed
*/
pred cold_rollup_prop1 {
  always (
   (some L1.forced_queue and some (L1.finalized_state' - L1.finalized_state))
     implies
          L1.forced_queue.first.tx in new_finalized_inputs
      and not L1.forced_queue.first.tx = L1.forced_queue'.first.tx 
  )
}
check {
  spec_L1_blacklist_eager implies cold_rollup_prop1 
  spec_L1_blacklist_soft implies cold_rollup_prop1 
} for 10

/* if finalized state didn't change then forced_queue only increased */
pred cold_rollup_prop2 {
  always (
   (L1.finalized_state = L1.finalized_state')
     implies
       ForcedInput :> L1.forced_queue.elems in ForcedInput :> L1.forced_queue'.elems
  )
}
check {
  spec_L1_blacklist_eager implies cold_rollup_prop2 
  spec_L1_blacklist_soft implies cold_rollup_prop2 
} for 10

/* if queue is not empty and didn't change then finalized_state didn' change */
pred cold_rollup_prop3 {
  always (
   (L1.forced_queue' = L1.forced_queue and some L1.forced_queue)
     implies
       L1.finalized_state = L1.finalized_state'
  )
}
check {
   spec_L1_blacklist_eager implies cold_rollup_prop3 
   spec_L1_blacklist_soft implies cold_rollup_prop3 
} for 10

/* forced txs which were not processed move down in the forced queue */
pred cold_rollup_prop4 {
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
check {
  spec_L1_blacklist_eager implies cold_rollup_prop4
  spec_L1_blacklist_soft implies cold_rollup_prop4
} for 5

/* forced txs which were not processed retain their relative order */
pred cold_rollup_prop7 {
 always (
    (some L1.forced_queue 
    and #L1.finalized_state < #L1.finalized_state') implies
    (all x, y : ForcedEvent |
      (x + y in L1.forced_queue.elems
       and x + y in L1.forced_queue'.elems
       and L1.forced_queue.idxOf[x] < L1.forced_queue.idxOf[y])
       implies 
        L1.forced_queue'.idxOf[x] < L1.forced_queue'.idxOf[y]
 ))
}
check {
  spec_L1_blacklist_eager implies cold_rollup_prop7
  spec_L1_blacklist_soft implies cold_rollup_prop7
} for 7

/* if forced input was in the forced queue and then disappeared from it then
 it was finalized */
pred cold_rollup_prop5 {
  always (
    all fi : ForcedInput | fi in L1.forced_queue.elems 
      implies always(fi not in L1.forced_queue.elems implies fi.tx in all_finalized_inputs)
  )
}
check {
  spec_L1_blacklist_eager implies cold_rollup_prop5
  spec_L1_blacklist_soft implies cold_rollup_prop5
} for 7


/* if input is finalized then it is not in the blacklist */
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
 } for 7

/* if censored input is in the head of the forced_queue 
   then finalized state will never change */
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



/* if univ is censored then no new inputs are ever finalized */
pred blacklist_prop5 {
  spec_all_censored implies always (no new_finalized_inputs)
}
check {
  spec_L1_blacklist_eager implies blacklist_prop5
  spec_L1_blacklist_soft implies blacklist_prop5
} for 5

/* blacklisted can never appear in the head position of the queue */
pred blacklist_prop6 {
 always (
    all x : Input | 
        not (x in L1.blacklist and x = L1.forced_queue.first.tx) 
  )
}
check {
  spec_L1_blacklist_eager implies blacklist_prop6
  spec_L1_blacklist_soft implies blacklist_prop6
 } for 7

/* all inputs which stand behind new blacklist policy are not blacklisted by it */
pred blacklist_prop7 {
    always (
      all x : ForcedBlacklistPolicy, y : ForcedInput |
         x in L1.forced_queue.elems
         and y in L1.forced_queue.elems
        and L1.forced_queue.idxOf[x] < L1.forced_queue.idxOf[y]
        implies y.tx not in x.predicate
    )
}
check {
  spec_L1_blacklist_eager implies blacklist_prop7
  spec_L1_blacklist_soft implies blacklist_prop7
} for 7


/*  if input got forced and there is no queued blacklisting policy 
    then the input is not in the `L1.blacklist` */
pred blacklist_prop8 {
    always (
      all y : ForcedInput |
         no L1.forced_queue.elems & ForcedBlacklistPolicy
         and y in L1.forced_queue.elems
        implies y.tx not in L1.blacklist
    )
}
check {
  spec_L1_blacklist_eager implies blacklist_prop8
  spec_L1_blacklist_soft implies blacklist_prop8
} for 7


/* if there upgrade was deployed (policy changed) then there
was upgrade announce, followed by timeout */
pred upgrade_prop1 {
  always (
    not L1.blacklist = L1.blacklist' implies
      once (
        some a : UpgradeAnnouncement | 
           a.blacklist_policy.predicate = L1.blacklist'
           and eventually (some t : Timeout | t.upgrade = a and 
              not L1.blacklist = a.blacklist_policy.predicate)
      )
  )
}

check {
  spec_L1_blacklist_soft implies upgrade_prop1
} for 7

/* after upgrade all forced inputs were finalized */
pred upgrade_prop2 {
  always (
    (not L1.blacklist = L1.blacklist') implies
      historically (
        all f : ForcedInput | 
           f in L1.forced_queue.elems implies
             eventually (
               f.tx in L1.finalized_state.elems.block_inputs.elems
             )
      )
  )  
}

check {
  spec_L1_blacklist_soft implies upgrade_prop2
} for 7

/* if policy changed then no ongoing upgrade is happening 
   (forced queue is unlocked, and rollup process is unlocked) */
pred upgrade_prop3 {
  always (
    (not L1.blacklist = L1.blacklist') implies
    (L1.ongoing_upgrade.blacklist_policy.predicate = L1.blacklist') and
    L1.ongoing_upgrade' = none
  )  
}
check {
  spec_L1_blacklist_soft implies upgrade_prop3
} for 7


/* as long as upgrade is ongoing L1.blacklist does not change */
pred upgrade_prop4 {
  always (
  all is : set Input |
    L1.blacklist = is 
    and some L1.ongoing_upgrade
    implies 
    (some L1.ongoing_upgrade) releases (L1.blacklist = is)
  )
    
}

check {
  spec_L1_blacklist_soft implies upgrade_prop4
} for 7

