module alloy/rollup_seq

var sig Input{} // inputs/transactions

// forced inputs is a subset because otherwise can badly interact 
// with policies, allow withdrawals)

// Stefanos: yes (block submitted to L1)
var sig Block {
 var block_inputs : seq Input
}

var abstract sig ForcedEvent {}
var sig ForcedInput extends ForcedEvent {
   var tx : one Input
}


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


one sig L1 {
  var finalized_state : seq Block,
  var forced_queue : seq ForcedEvent,
  var commitments : set Commitment,
  var proofs : set Proof
// var censored : set Input
}{ 
  not finalized_state.hasDups
  not forced_queue.hasDups
}

fun all_finalized_inputs : set Input {
  { i : Input | i in L1.finalized_state.elems.block_inputs.elems } 
}



pred receive_commitment[c : Commitment] {
  // no dup	licates
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
}

pred receive_forced[f : ForcedEvent] {
 no L1.forced_queue.idxOf[f]
 f.tx not in all_finalized_inputs
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
}



pred rollup_simple[c: Commitment, p:Proof] {
    c -> p in L1.commitments -> L1.proofs
    c.state = p.state
    c.diff  = p.diff
    c.state = L1.finalized_state

    (no L1.finalized_state.idxOf[c.diff])
    some L1.forced_queue 
       implies some c.diff.block_inputs.idxOf[L1.forced_queue.first.tx]

    L1.finalized_state' = L1.finalized_state.add[p.diff]
    L1.proofs' = L1.proofs - p
    L1.commitments' = L1.commitments - c

    no (L1.forced_queue'.elems.tx & p.diff.block_inputs.elems)
    all x : ForcedEvent | (x.tx not in p.diff.block_inputs.elems  
                 and (some L1.forced_queue.idxOf[x.tx]))
       implies L1.forced_queue'.idxOf[x.tx] < L1.forced_queue.idxOf[x.tx]
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
  forced_queue = forced_queue'
}

// event names
enum Event { Stutter, 
             ReceiveComm, 
             ReceiveProof, 
             ReceiveForced, 
             ProcessSimple 
           }

// all possible receive_commitment events
fun receive_commitment_happens : Event -> Commitment {
  { e : ReceiveComm, c: Commitment | receive_commitment[c] }
}

fun receive_proof_happens : Event -> Proof {
  { e : ReceiveProof, p: Proof | receive_proof[p] }
}

fun receive_forced_happens : Event -> ForcedEvent {
  { e : ReceiveForced, p: ForcedEvent | receive_forced[p] }
}

fun stutter_happens : set Event {
  { e: Stutter | stutter }
}

fun rollup_simple_happens : Event -> Commitment -> Proof {
  { e : ProcessSimple, c: Commitment, p: Proof | rollup_simple[c,p] }
}

fun events : set Event {
   rollup_simple_happens.Proof.Commitment 
   + stutter_happens 
   + receive_forced_happens.ForcedEvent
   + receive_proof_happens.Proof
   + receive_commitment_happens.Commitment
}

fact traces { // possible traces
  always some events
//  always (some s : set Input | zzz[s])
}

check at_most_one_event {
  always lone events
} for 5

// start with no finilized state
fact {
  no finalized_state
  no forced_queue
//  no commitments
//  no proofs
} 

// final state grows monotonically
assert finalized_state_monotonic { 
  always (finalized_state in finalized_state')
}
check finalized_state_monotonic for 5


fun new_finalized_inputs : set Input {
  L1.finalized_state'.elems.block_inputs.elems - L1.finalized_state.elems.block_inputs.elems
}

// if forced_queue is non-empty and something was added to the finalized-state
// then the head of the forced queue was processed
assert cold_rollup_prop1 {
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
  always (
   (L1.finalized_state = L1.finalized_state')
     implies
       L1.forced_queue in L1.forced_queue'
  )
}
check cold_rollup_prop2 for 5

// if queue is not empty and didn't change then finalized_state didn' change
assert cold_rollup_prop3 {
  always (
   (L1.forced_queue' = L1.forced_queue and some L1.forced_queue)
     implies
       L1.finalized_state = L1.finalized_state'
  )
}
check cold_rollup_prop3 for 5


// forced txs move down in the forced queue
assert cold_rollup_prop5 {
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
check cold_rollup_prop5 for 5

// if something gets into finilized_state then at some moment 
// there was a proof and a commitment for it
assert finalized_state_correct { 
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
check finalized_state_correct for 3

run two_process_in_a_row {
  eventually (some rollup_simple_happens 
                  and after some rollup_simple_happens)
} for 5

run { 
 eventually (#forced_queue = 2 and #finalized_state = 1 ; #finalized_state = 2)
} for 10 


