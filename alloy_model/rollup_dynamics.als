module alloy/rollup_dynamics

open alloy/rollup_data_model


pred receive_commitment[c : Commitment] {
  // no duplicates
  no c & L1.commitments 
  // committed state is longer than current
  c.state.subseq[0,#L1.finalized_state] = L1.finalized_state 

  // extending the set of commitments to the state transition
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
}

pred receive_proof[p : Proof] {
  no p & L1.proofs
  p.state.subseq[0,#L1.finalized_state] = L1.finalized_state 

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
}

pred receive_forced_broken[f : ForcedEvent, bl : set Input] {
 no L1.forced_queue.idxOf[f]
 L1.forced_queue' = L1.forced_queue.add[f]

 f in ForcedInput implies f.tx not in bl and f.tx not in all_finalized_inputs
 f in ForcedBlacklistPolicy implies no (ForcedBlacklistPolicy & L1.forced_queue.elems)

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
}

pred receive_forced[f : ForcedEvent, bl : set Input] {
 no L1.forced_queue.idxOf[f]

// f in ForcedInput implies (f.tx not in bl and f.tx not in all_finalized_inputs 
//   and (f.tx not in L1.forced_queue.elems.predicate))
  f in ForcedInput implies (f.tx not in all_finalized_inputs 
     and (some L1.forced_queue.elems.predicate 
              implies f.tx not in L1.forced_queue.elems.predicate else f.tx not in bl))
  
 f in ForcedBlacklistPolicy implies no (ForcedBlacklistPolicy & L1.forced_queue.elems)

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
}



pred rollup_simple[c: Commitment, p:Proof, bl : set Input] {
    // commitments and proofs are scheduled
    c in L1.commitments  
    p in L1.proofs
    // commitment and proof correspond to finalized state and transition
    c.state = p.state
    c.diff  = p.diff
    c.state = L1.finalized_state
    // currently blacklisted stuff is not processed
    no (bl & c.diff.block_inputs.elems) 
    // not processing the block if it is already finalized
    (no L1.finalized_state.idxOf[c.diff])
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
    L1.proofs' = L1.proofs - p
    L1.commitments' = L1.commitments - c

    // processed elements are deletes form forced queue
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
    // no new stuff appears
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
}

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
}

// system specifications
fact {
  no finalized_state
  no forced_queue
} 

// event names
enum Event { Stutter, 
             ReceiveComm, 
             ReceiveProof, 
             ReceiveForced, 
             ProcessSimple,
             UpdateBlacklist
           }

// all possible receive_commitment events
fun receive_commitment_happens : Event -> Commitment {
  { e : ReceiveComm, c: Commitment | receive_commitment[c] }
}

fun receive_proof_happens : Event -> Proof {
  { e : ReceiveProof, p: Proof | receive_proof[p] }
}

fun receive_forced_happens[bl : set Input] : Event -> ForcedEvent {
  { e : ReceiveForced, p: ForcedEvent | receive_forced[p,bl] }
}

fun stutter_happens : set Event {
  { e: Stutter | stutter }
}

fun blacklist_update_happens : Event -> ForcedBlacklistPolicy {
  { e: UpdateBlacklist, f : ForcedBlacklistPolicy | update_blacklist[f] }
}

fun rollup_simple_happens[bl : set Input] : Event -> Commitment -> Proof {
  { e : ProcessSimple, c: Commitment, p: Proof | rollup_simple[c,p,bl] }
}

fun events[bl : set Input] : set Event {
   rollup_simple_happens[bl].Proof.Commitment 
   + stutter_happens 
   + blacklist_update_happens.ForcedBlacklistPolicy
   + receive_forced_happens[bl].ForcedEvent
   + receive_proof_happens.Proof
   + receive_commitment_happens.Commitment
}

pred spec_no_censorship { 
  always some events[none]
}

pred spec_L1_blacklist { 
  always some events[L1.blacklist]
}

pred spec_all_censored {
  always some events[univ]
}



