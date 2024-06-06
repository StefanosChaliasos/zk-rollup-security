module alloy/rollup_dynamics

open alloy/rollup_data_model

pred receive_commitment[c : Commitment] {
  // no duplicates
  no c & L1.commitments 
  // committed state is longer than the currently finalized state
  c.state.subseq[0,sub[#L1.finalized_state,1]] = L1.finalized_state 

  // extending the set of commitments
  L1.commitments' = L1.commitments + c

  // frame conditions
  Proof = Proof'
  Commitment = Commitment'
  proofs = proofs'
  finalized_state = finalized_state'
  state = state'
  diff = diff'
  forced_queue = forced_queue'
  block_inputs = block_inputs'
  ForcedEvent = ForcedEvent'
  tx = tx'
  blacklist = blacklist'
  predicate = predicate'
  BlacklistUpdateAnnouncement = BlacklistUpdateAnnouncement'
  blacklist_policy = blacklist_policy'
  Timeout = Timeout'
  upgrade = upgrade'
  ongoing_upgrade = ongoing_upgrade'
}

pred receive_proof[p : Proof] {
  no p & L1.proofs
  p.state.subseq[0,sub[#L1.finalized_state,1]] = L1.finalized_state 

  // extending the set of proofs
  L1.proofs' = L1.proofs + p

  // frame conditions
  Proof = Proof'
  Commitment = Commitment'
  commitments = commitments'
  finalized_state = finalized_state'
  state = state'
  diff = diff'
  forced_queue = forced_queue'
  block_inputs = block_inputs'
  ForcedEvent' = ForcedEvent
  tx = tx'
  blacklist = blacklist'
  predicate = predicate'
  BlacklistUpdateAnnouncement = BlacklistUpdateAnnouncement'
  blacklist_policy = blacklist_policy'
  Timeout = Timeout'
  upgrade = upgrade'
  ongoing_upgrade = ongoing_upgrade'
}

pred receive_forced[f : ForcedEvent] {
  // no duplicates
  no L1.forced_queue.idxOf[f]
  // forbid new forced inputs if we are upgrading but queueing finished
  upgrade_in_progress implies upgrade_queueing
 
  // ignore input if previously finalized
  // if blacklist policy is in the forced queue then make sure that f complies
  // otherwise make sure that f is not in the currently active blacklist
  f in ForcedInput implies (f.tx not in all_finalized_inputs 
     and (some L1.forced_queue.elems.predicate 
              implies f.tx not in L1.forced_queue.elems.predicate 
                  else f.tx not in L1.blacklist))
  
  // ensure only one blacklisting policy in the forced queue
  f in ForcedBlacklistPolicy implies no (ForcedBlacklistPolicy & L1.forced_queue.elems)

  // forced input
  L1.forced_queue' = L1.forced_queue.add[f]

  // frame conditions
  commitments' = commitments
  Proof = Proof'
  Input = Input'
  Block = Block'
  Commitment = Commitment'
  proofs = proofs'
  finalized_state = finalized_state'
  block_inputs = block_inputs'
  state = state'
  diff = diff'
  ForcedEvent' = ForcedEvent
  tx = tx'
  blacklist = blacklist'
  predicate = predicate'
  BlacklistUpdateAnnouncement = BlacklistUpdateAnnouncement'
  blacklist_policy = blacklist_policy'
  Timeout = Timeout'
  upgrade = upgrade'
  ongoing_upgrade = ongoing_upgrade'
}

pred rollup_process {
  some c : Commitment , p : Proof | rollup_simple[c,p]
}

pred rollup_simple[c: Commitment, p:Proof] {
    // forbid to finalize new blocks if we are upgrading but not processing
    upgrade_in_progress implies upgrade_forced_queue_processing

    // commitments and proofs are scheduled
    c in L1.commitments  
    p in L1.proofs
    // commitment and proof correspond to finalized state and transition
    c.state = p.state
    c.diff  = p.diff
    c.state = L1.finalized_state
    // currently blacklisted inputs are not processed
    no (L1.blacklist & c.diff.block_inputs.elems) 
    // not processing the block if it is already finalized
    no L1.finalized_state.idxOf[c.diff]

    // the head of forced queue is in the diff
    some L1.forced_queue
       implies 
        (L1.forced_queue.first in ForcedInput 
         and some c.diff.block_inputs.idxOf[L1.forced_queue.first.tx])

    // only allow to process inputs which are in front of the next blacklist policy
    // absence of that condition generates interesting counterexamples
    all x : ForcedBlacklistPolicy, y : ForcedInput | 
        some L1.forced_queue 
     and x in L1.forced_queue.elems 
     and y.tx in L1.forced_queue.elems.tx 
     and y.tx in c.diff.block_inputs.elems  
          implies L1.forced_queue.idxOf[y] < L1.forced_queue.idxOf[x]
      
    // updates to L1 state
    L1.finalized_state' = L1.finalized_state.add[p.diff]

    // cleanup the scheduled proofs/commitments
    L1.proofs' = L1.proofs - (p + { q : Proof | #q.state < #L1.finalized_state })
    L1.commitments' = L1.commitments - (c + { q : Commitment | #q.state < #L1.finalized_state })

    // below we are formalizing what it means to remove multiple elements from the sequence

    // processed elements are deleted form forced queue
    no (L1.forced_queue'.elems.tx & p.diff.block_inputs.elems)
    // forced inputs are preserved and moved 
    all x : ForcedInput | (x.tx not in p.diff.block_inputs.elems  
                 and (some L1.forced_queue.idxOf[x]))
       implies L1.forced_queue'.idxOf[x] < L1.forced_queue.idxOf[x]
              and (some L1.forced_queue'.idxOf[x])
    all x : ForcedBlacklistPolicy | (
                 (some L1.forced_queue.idxOf[x]))
       implies L1.forced_queue'.idxOf[x] < L1.forced_queue.idxOf[x]
                and (some L1.forced_queue'.idxOf[x])
    // relative positions do not change
    all x, y : ForcedEvent | some L1.forced_queue'.idxOf[x] and some L1.forced_queue'.idxOf[y]
        and L1.forced_queue.idxOf[x] < L1.forced_queue.idxOf[y] implies
            L1.forced_queue'.idxOf[x] < L1.forced_queue'.idxOf[y]
    // no new events appears
    all x : ForcedEvent | x not in L1.forced_queue.elems
       implies x not in L1.forced_queue'.elems

    // frame conditions
    Proof = Proof'
    ForcedEvent = ForcedEvent'
    Commitment = Commitment'
    state = state'
    block_inputs = block_inputs'
    diff = diff'
    Input = Input'
    Block = Block'
    tx = tx'
    blacklist = blacklist'
    predicate = predicate'
    BlacklistUpdateAnnouncement = BlacklistUpdateAnnouncement'
    blacklist_policy = blacklist_policy'
    Timeout = Timeout'
    upgrade = upgrade'
    ongoing_upgrade = ongoing_upgrade'
}



// do nothing
pred stutter {
  commitments' = commitments
  Proof = Proof'
  Input = Input'
  Block = Block'
  ForcedEvent = ForcedEvent'
  Commitment = Commitment'
  proofs = proofs'
  finalized_state = finalized_state'
  state = state'
  block_inputs = block_inputs'
  diff = diff'
  tx = tx'
  blacklist = blacklist'
  forced_queue = forced_queue'
  predicate = predicate'
  BlacklistUpdateAnnouncement = BlacklistUpdateAnnouncement'
  blacklist_policy = blacklist_policy'
  Timeout = Timeout'
  upgrade = upgrade'
  ongoing_upgrade = ongoing_upgrade'
}

// update the blacklist
pred update_blacklist[f : ForcedBlacklistPolicy] {
  L1.forced_queue.first = f

  L1.blacklist' = L1.forced_queue.first.predicate
  L1.forced_queue' = L1.forced_queue.delete[0]


  commitments' = commitments
  Proof = Proof'
  Input = Input'
  Block = Block'
  ForcedEvent = ForcedEvent'
  Commitment = Commitment'
  proofs = proofs'
  finalized_state = finalized_state'
  state = state'
  block_inputs = block_inputs'
  diff = diff'
  tx = tx'
  predicate = predicate'
  BlacklistUpdateAnnouncement = BlacklistUpdateAnnouncement'
  blacklist_policy = blacklist_policy'
  Timeout = Timeout'
  upgrade = upgrade'
  ongoing_upgrade = ongoing_upgrade'
}

// announce the upgrade
pred upgrade_init[f : UpgradeAnnouncement] {
  L1.ongoing_upgrade = none
  L1.ongoing_upgrade' = f
  (f not in Timeout.upgrade)
  
  commitments' = commitments
  Proof = Proof'
  Input = Input'
  Block = Block'
  ForcedEvent = ForcedEvent'
  Commitment = Commitment'
  proofs = proofs'
  finalized_state = finalized_state'
  state = state'
  block_inputs = block_inputs'
  forced_queue' = forced_queue
  diff = diff'
  tx = tx'
  predicate = predicate'
  BlacklistUpdateAnnouncement = BlacklistUpdateAnnouncement'
  blacklist_policy' = blacklist_policy
  blacklist' = blacklist
  Timeout = Timeout'
  upgrade = upgrade' 
}

// timeout happened [argument t comes from the set next step]
pred upgrade_timeout[t : Timeout] {
  t.upgrade' = L1.ongoing_upgrade

  Timeout' - t = Timeout
  Timeout.upgrade' = Timeout'.upgrade

  commitments' = commitments
  Proof = Proof'
  Input = Input'
  Block = Block'
  ForcedEvent = ForcedEvent'
  Commitment = Commitment'
  proofs = proofs'
  finalized_state = finalized_state'
  state = state'
  block_inputs = block_inputs'
  diff = diff'
  tx = tx'
  blacklist = blacklist'
  forced_queue = forced_queue'
  predicate = predicate'
  BlacklistUpdateAnnouncement = BlacklistUpdateAnnouncement'
  blacklist_policy = blacklist_policy'
  ongoing_upgrade = ongoing_upgrade'
}

// deploy the upgrade
pred upgrade_deploy {
  upgrade_forced_queue_processing_finished

  L1.blacklist' = L1.ongoing_upgrade.blacklist_policy.predicate
  L1.ongoing_upgrade' = none

  Timeout' = Timeout
  upgrade' = upgrade
  commitments' = commitments
  Proof = Proof'
  Input = Input'
  Block = Block'
  ForcedEvent = ForcedEvent'
  Commitment = Commitment'
  proofs = proofs'
  finalized_state = finalized_state'
  state = state'
  block_inputs = block_inputs'
  diff = diff'
  tx = tx'
  forced_queue = forced_queue'
  predicate = predicate'
  BlacklistUpdateAnnouncement = BlacklistUpdateAnnouncement'
  blacklist_policy = blacklist_policy'
}

// system specifications
fact {
  no finalized_state
  no forced_queue
  no Timeout
  no ongoing_upgrade
} 
//fact {  
  // no (L1.forced_queue.tx & L1.blacklist)
  // no (L1.forced_queue & ForcedEvent)
  // no Timeout
  // no ongoing_upgrade
//} 

// event names
enum Event { Stutter, 
             ReceiveComm, 
             ReceiveProof, 
             ProcessSimple,

             ReceiveForced, 
             UpdateBlacklist,

             UpgradeInit,
             UpgradeTimeout,
             UpgradeDeploy
           }


fun upgrade_events : set Event {
  UpgradeInit + UpgradeTimeout + UpgradeDeploy 
}


// all possible receive_commitment events
fun stutter_happens : set Event {
  { e: Stutter | stutter }
}

fun receive_commitment_happens : Event -> Commitment {
  { e : ReceiveComm, c: Commitment | receive_commitment[c] }
}

fun receive_proof_happens : Event -> Proof {
  { e : ReceiveProof, p: Proof | receive_proof[p] }
}

fun receive_forced_happens : Event -> ForcedEvent {
  { e : ReceiveForced, p: ForcedEvent | receive_forced[p] }
}

fun blacklist_update_happens : Event -> ForcedBlacklistPolicy {
  { e: UpdateBlacklist, f : ForcedBlacklistPolicy | update_blacklist[f] }
}

fun rollup_simple_happens : Event  {
  { e : ProcessSimple | rollup_process }
}

fun upgrade_init_happens : Event -> UpgradeAnnouncement {
  { e : UpgradeInit, u : UpgradeAnnouncement | upgrade_init[u] }
}

fun upgrade_timeout_happens : Event -> Timeout {
  { e : UpgradeTimeout, t : Timeout' | upgrade_timeout[t] }
}

fun upgrade_deploy_happens : Event  {
  { e : UpgradeDeploy | upgrade_deploy }
}

fun events : set Event {
  // simple 
   rollup_simple_happens
   + receive_proof_happens.Proof
   + receive_commitment_happens.Commitment   
   + stutter_happens 
   
   // forced
   + receive_forced_happens.ForcedEvent

   // eager blacklist
   + blacklist_update_happens.ForcedBlacklistPolicy

   // upgradeability with soft blacklisting
   + upgrade_init_happens.UpgradeAnnouncement
   + upgrade_timeout_happens.Timeout'
   + upgrade_deploy_happens
}


pred spec_simple { 
  always (no L1.blacklist)
  always (no L1.forced_queue and no ForcedEvent and no UpgradeAnnouncement)
  always some (events - UpdateBlacklist - upgrade_events - ReceiveForced)
}

pred spec_forced_queue { 
  always (no L1.blacklist and no UpgradeAnnouncement)
  always some (events - UpdateBlacklist - upgrade_events)
}

pred spec_blacklist_eager { 
  always some (events - upgrade_events)
}

pred spec_blacklist_soft { 
  always (some events and no ForcedBlacklistPolicy & L1.forced_queue.elems)
}

pred spec_all_censored {
  always (L1.blacklist = univ)
  always some events
}