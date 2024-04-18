module alloy/rollup_seq

// Inputs and Blocks
var sig Input{}

var sig Block {
 var block_inputs : seq Input
}

// Commitment and Proof objects
var abstract sig ZKObject {
  var state : seq Block,
  var diff : one Block // Stefanos: possible to have diff: seq Block
}
var sig Proof extends ZKObject{}{
  not state.hasDups
  diff not in state.elems
}
var sig Commitment extends ZKObject{}{
  not state.hasDups
  diff not in state.elems
}

// Forced events
var abstract sig ForcedEvent {}

var sig ForcedInput extends ForcedEvent {
   var tx : one Input
}
var sig ForcedBlacklistPolicy extends ForcedEvent {
   var predicate : set Input
}

// L1 state of the rollup
one sig L1 {
  var finalized_state : seq Block,
  var forced_queue : seq ForcedEvent,
  var commitments : set Commitment,
  var proofs : set Proof,
  var blacklist : set Input
}{ 
  not finalized_state.hasDups
  not forced_queue.hasDups
}

fun all_finalized_inputs : set Input {
  { i : Input | i in L1.finalized_state.elems.block_inputs.elems } 
}

fun new_finalized_inputs : set Input {
  L1.finalized_state'.elems.block_inputs.elems 
      - L1.finalized_state.elems.block_inputs.elems
}


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



// system specifications
fact {
  no finalized_state
  no forced_queue
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

check at_most_one_event {
  spec_no_censorship implies always lone events[none]
  spec_L1_blacklist  implies always lone events[L1.blacklist]
} for 5


// if something gets into finilized_state then at some moment 
// there was a proof and a commitment for it
assert rollup_process_prop1 { 
 spec_L1_blacklist implies
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
  spec_L1_blacklist implies always (finalized_state in finalized_state')
}
check rollup_process_prop2 for 5

// if forced_queue is non-empty and something was added to the finalized-state
// then the head of the forced queue was processed
assert cold_rollup_prop1 {
 spec_L1_blacklist implies
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
 spec_L1_blacklist implies
  always (
   (L1.finalized_state = L1.finalized_state')
     implies
       ForcedInput :> L1.forced_queue.elems in ForcedInput :> L1.forced_queue'.elems
  )
}
check cold_rollup_prop2 for 5

// if queue is not empty and didn't change then finalized_state didn' change
assert cold_rollup_prop3 {
 spec_L1_blacklist implies
  always (
   (L1.forced_queue' = L1.forced_queue and some L1.forced_queue)
     implies
       L1.finalized_state = L1.finalized_state'
  )
}
check cold_rollup_prop3 for 5

// forced txs which were not processed move down in the forced queue
assert cold_rollup_prop4 {
 spec_L1_blacklist implies
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

// blacklist works
assert blacklist_prop1 {
  spec_L1_blacklist implies
  always(
    all x : Input | x in L1.finalized_state'.elems.block_inputs.elems 
                 and x not in L1.finalized_state.elems.block_inputs.elems
          implies x not in L1.blacklist
  )
}
check blacklist_prop1 for 5

// if something censored is in the head of the forced_queue then finalized state will never change
assert blacklist_prop2 {
  spec_L1_blacklist implies
    always (
    all x : Input | (x in L1.blacklist and x = L1.forced_queue.first.tx)
        implies always (L1.finalized_state = L1.finalized_state')
  )
}
check blacklist_prop2 for 5

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

run { 
 eventually (#forced_queue = 2 and #finalized_state = 1 ; #finalized_state = 2)
} for 10

run blaeacklist {
 spec_L1_blacklist 
 #blacklist = 0
 eventually (#blacklist = 1 ; #blacklist = 2)
}

