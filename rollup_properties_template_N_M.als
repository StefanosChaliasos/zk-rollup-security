module alloy/rollup_properties

open alloy/rollup_data_model
open alloy/rollup_dynamics


/* SRP1: Event Granularity - at most one event happens at a time */
check c_srp1 {
  spec_simple implies always lone events
  spec_forced_queue implies always lone events
  spec_blacklist_eager implies always lone events
  spec_blacklist_soft implies always lone events
} for {{N}} but 1..{{M}} steps

/* SRP2: Monotonic State - final state grows monotonically */
pred srp2 { 
  always (finalized_state in finalized_state')
}
check c_srp2 {
  spec_simple implies srp2
  spec_forced_queue implies srp2
  spec_blacklist_eager implies srp2
  spec_blacklist_soft implies srp2
} for {{N}} but 1..{{M}} steps

/* SRP3: Justified State - if block gets finalized then at some moment 
   there was a proof and a commitment for it which corresponded to the
   current state */
pred srp3 { 
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
check c_srp3 {
  spec_simple implies srp3
  spec_forced_queue implies srp3
  spec_blacklist_eager implies srp3
  spec_blacklist_soft implies srp3
} for {{N}} but 1..{{M}} steps

/* SRP4: State Progression Validity - The commitment/proof which is smaller than current state never 
   gets successfully processed.
*/
pred srp4 { 
 always(
   all c : Commitment, p : Proof | 
      #c.state < #L1.finalized_state
     implies
      not (rollup_simple[c,p])
 )
}

check c_srp4 {
  spec_simple implies srp4
  spec_forced_queue implies srp4
  spec_blacklist_eager implies srp4
  spec_blacklist_soft implies srp4
} for {{N}} but 1..{{M}} steps


/* FQP1: Guaranteed Processing - if forced_queue is non-empty and something was added to the finalized-state
   then the head of the forced queue was processed
*/
pred fqp1 {
  always (
   (some L1.forced_queue and some (L1.finalized_state' - L1.finalized_state))
     implies
          L1.forced_queue.first.tx in new_finalized_inputs
      and not L1.forced_queue.first.tx = L1.forced_queue'.first.tx 
  )
}
check c_fqp1 {
  spec_forced_queue implies fqp1
  spec_blacklist_eager implies fqp1 
  spec_blacklist_soft implies fqp1 
} for {{N}} but 1..{{M}} steps

/* FQP2: Forced Queue Stable - if finalized state didn't change then forced_queue only increased */
pred fqp2 {
  always (
   (L1.finalized_state = L1.finalized_state')
     implies
       ForcedInput :> L1.forced_queue.elems in ForcedInput :> L1.forced_queue'.elems
  )
}
check c_fqp2 {
  spec_forced_queue implies fqp2
  spec_blacklist_eager implies fqp2 
  spec_blacklist_soft implies fqp2 
} for {{N}} but 1..{{M}} steps

/* FQP3: State Invariant - if queue is not empty and didn't change then finalized_state didn't change */
pred fqp3 {
  always (
   (L1.forced_queue' = L1.forced_queue and some L1.forced_queue)
     implies
       L1.finalized_state = L1.finalized_state'
  )
}
check c_fqp3 {
  spec_forced_queue implies fqp3
  spec_blacklist_eager implies fqp3 
  spec_blacklist_soft implies fqp3 
} for {{N}} but 1..{{M}} steps

/* FQP4: Forced Inputs Progress - forced txs which were not processed move down in the forced queue */
pred fqp4 {
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
check c_fqp4 {
  spec_forced_queue implies fqp4
  spec_blacklist_eager implies fqp4
  spec_blacklist_soft implies fqp4
} for {{N}} but 1..{{M}} steps

/* FQP5: Order Preservation - forced txs which were not processed retain their relative order */
pred fqp5 {
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
check c_fqp5 {
  spec_forced_queue implies fqp5
  spec_blacklist_eager implies fqp5
  spec_blacklist_soft implies fqp5
} for {{N}} but 1..{{M}} steps
/* FQP6: Finalization Confirmation - if forced input was in the forced queue and then disappeared from it then
 it was finalized */
pred fqp6 {
  always (
    all fi : ForcedInput | fi in L1.forced_queue.elems 
      implies always(fi not in L1.forced_queue.elems implies fi.tx in all_finalized_inputs)
  )
}
check c_fqp6 {
  spec_forced_queue implies fqp6
  spec_blacklist_eager implies fqp6
  spec_blacklist_soft implies fqp6
} for {{N}} but 1..{{M}} steps

/* BP1: Non-blacklisted Finalization - if input is finalized then it is not in the blacklist */
pred bp1 {
  always(
    all x : Input | 
       x in L1.finalized_state'.elems.block_inputs.elems 
   and x not in L1.finalized_state.elems.block_inputs.elems
          implies x not in L1.blacklist
  )
}
check c_bp1 {
  spec_blacklist_eager implies bp1
  spec_blacklist_soft implies bp1
 } for {{N}} but 1..{{M}} steps

/* BP2: Forced Queue Integrity under Censorship - if censored input is in the head of the forced_queue 
   then finalized state will never change */
pred bp2 {
    always (
    all x : Input | (x in L1.blacklist and x = L1.forced_queue.first.tx)
        implies always (L1.finalized_state = L1.finalized_state')
  )
}
check c_bp2 {
  spec_blacklist_eager implies bp2 
  spec_blacklist_soft implies bp2 
} for {{N}} but 1..{{M}} steps

/* BP3: Head Position Security - blacklisted can never appear in the head position of the queue */
pred bp3 {
 always (
    all x : Input | 
        not (x in L1.blacklist and x = L1.forced_queue.first.tx) 
  )
}
check c_bp3 {
  spec_blacklist_eager implies bp3
  spec_blacklist_soft implies bp3
 } for {{N}} but 1..{{M}} steps

/* BP4: Future Policy Compliance - all inputs which stand behind new blacklist policy are not blacklisted by it */
pred bp4 {
    always (
      all x : ForcedBlacklistPolicy, y : ForcedInput |
         x in L1.forced_queue.elems
         and y in L1.forced_queue.elems
        and L1.forced_queue.idxOf[x] < L1.forced_queue.idxOf[y]
        implies y.tx not in x.predicate
    )
}
check c_bp4 {
  spec_blacklist_eager implies bp4
  spec_blacklist_soft implies bp4
} for {{N}} but 1..{{M}} steps


/*  if input got forced and there is no queued blacklisting policy 
    then the input is not in the `L1.blacklist` */
pred bp5 {
    always (
      all y : ForcedInput |
         no L1.forced_queue.elems & ForcedBlacklistPolicy
         and y in L1.forced_queue.elems
        implies y.tx not in L1.blacklist
    )
}
check c_bp5 {
  spec_blacklist_eager implies bp5
  spec_blacklist_soft implies bp5
} for {{N}} but 1..{{M}} steps

/* Helper property: if univ is censored then no new inputs are ever finalized */
pred blacklist_prop_all_censored {
  spec_all_censored implies always (no new_finalized_inputs)
}
check c_blacklist_prop_all_censored {
  spec_blacklist_eager implies blacklist_prop_all_censored
  spec_blacklist_soft implies blacklist_prop_all_censored
} for {{N}} but 1..{{M}} steps

/* UP1: Consistency of Upgrade Announcement, Timeout, and Enforcement - if the upgrade was deployed (policy changed) then there
   is upgrade announce, followed by timeout */
pred up1 {
always (
  all is : set Input | L1.blacklist = is and 
  not L1.blacklist = L1.blacklist'  
     implies 
       some x : UpgradeAnnouncement | L1.ongoing_upgrade = x and
        once (L1.ongoing_upgrade = none and
              L1.ongoing_upgrade' = x  and
              L1.blacklist = is and
              (no { t : Timeout | t.upgrade = x })
        and ((some t : Timeout | t.upgrade = x)  
               releases L1.blacklist = is)
              )
)
}

check c_up1 {
  spec_blacklist_soft implies up1
} for {{N}} but 1..{{M}} steps

/* UP2: Finalization of Forced Inputs before the Upgrade - after upgrade all forced inputs were finalized */
pred up2 {
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

check c_up2 {
  spec_blacklist_soft implies up2
} for {{N}} but 1..{{M}} steps

/* UP3: Post-Upgrade System Integrity - if policy changed then no ongoing upgrade is happening 
   (forced queue is unlocked, and rollup process is unlocked) */
pred up3 {
  always (
    (not L1.blacklist = L1.blacklist') implies
    (L1.ongoing_upgrade.blacklist_policy.predicate = L1.blacklist') and
    L1.ongoing_upgrade' = none
  )  
}
check c_up3 {
  spec_blacklist_soft implies up3
} for {{N}} but 1..{{M}} steps

/* UP4: Consistency of Blacklisting During Upgrades - as long as upgrade is ongoing L1.blacklist does not change */
pred up4 {
  always (
  all is : set Input |
    L1.blacklist = is 
    and some L1.ongoing_upgrade
    implies 
    (some L1.ongoing_upgrade) releases (L1.blacklist = is)
  )
    
}

check c_up4 {
  spec_blacklist_soft implies up4
} for {{N}} but 1..{{M}} steps