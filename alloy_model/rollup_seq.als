module alloy/rollup_seq

var sig Input{} // inputs/transactions

var sig Forced in Input{} // in or extends?

// can block be empty?
// can block contain same input more than once?
var sig Block {
 var block_inputs : seq Input
}{ 
 #block_inputs = #block_inputs.elems // inputs never repeat in the block?
}

// can diff be more than one block?
var abstract sig ZKObject {
  var state : seq Block,
  var diff : one Block
}

var sig Proof extends ZKObject{}
var sig Commitment extends ZKObject{}

one sig L1 {
  var finalized_state : seq Block,
  var forced_queue : seq Forced,
  var commitments : set Commitment,
  var proofs : set Proof
}{ 
  #finalized_state = #finalized_state.elems // blocks never repeat?
}

pred receive_commitment[c : Commitment] {
  no c & L1.commitments  // no duplicates

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
  Forced = Forced'
}

pred receive_proof[p : Proof] {
  no p & L1.proofs // no duplicates

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
  Forced = Forced'
}

pred receive_forced[f : Forced] {
 no L1.forced_queue.idxOf[f]
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
 Forced = Forced'
}



pred rollup_simple[c: Commitment, p:Proof] {
    c -> p in L1.commitments -> L1.proofs
    c.state = p.state
    c.diff  = p.diff
    c.state = L1.finalized_state
    (no L1.finalized_state.idxOf[c.diff])
    some L1.forced_queue implies some c.diff.block_inputs.idxOf[L1.forced_queue.first]

    L1.finalized_state' = L1.finalized_state.add[p.diff]
    L1.proofs' = L1.proofs - p
    L1.commitments' = L1.commitments - c

    no (L1.forced_queue'.elems & p.diff.block_inputs.elems)
    all x : Forced | (x not in p.diff.block_inputs.elems  
                 and (some L1.forced_queue.idxOf[x]))
       implies L1.forced_queue'.idxOf[x] < L1.forced_queue.idxOf[x]
    all x : Forced | x not in L1.forced_queue.elems implies x not in L1.forced_queue'.elems
    not L1.forced_queue'.hasDups

    Proof = Proof'
    Forced = Forced'
    Commitment = Commitment'
    state = state'
    block_inputs = block_inputs'
    diff = diff'

}

pred stutter {
  commitments' = commitments
  Proof = Proof'
  Input = Input'
  Block = Block'
  Forced = Forced'
  Commitment = Commitment'
  proofs = proofs'
  finalized_state = finalized_state'
  state = state'
  block_inputs = block_inputs'
  diff = diff'
  forced_queue = forced_queue'
}

enum Event { Stutter, ReceiveComm, ReceiveProof, ReceiveForced, ProcessSimple } // event names

fun receive_commitment_happens : Event -> Commitment {
  { e : ReceiveComm, c: Commitment | receive_commitment[c] }
}

fun receive_proof_happens : Event -> Proof {
  { e : ReceiveProof, p: Proof | receive_proof[p] }
}

fun receive_forced_happens : Event -> Forced {
  { e : ReceiveForced, p: Forced | receive_forced[p] }
}

fun stutter_happens : set Event {
  { e: Stutter | stutter }
}

fun rollup_simple_happens : Event -> Commitment -> Proof {
  { e : ProcessSimple, c: Commitment , p : Proof | rollup_simple[c,p] }
}



fun events : set Event {
   rollup_simple_happens.Proof.Commitment 
   + stutter_happens 
   + receive_forced_happens.Forced
   + receive_proof_happens.Proof
   + receive_commitment_happens.Commitment
}

fact traces { // possible traces
  always some events
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

assert finalized_state_monotonic { // final state grows monotonically
  always (finalized_state in finalized_state')
}
check finalized_state_monotonic for 5

assert cold_rollup_prop1 {
  always (
   (some L1.forced_queue and  some (L1.finalized_state' - L1.finalized_state))
     implies
         some L1.finalized_state'.elems.block_inputs.idxOf[L1.forced_queue.first]
  )
}
check cold_rollup_prop1 for 7

assert cold_rollup_prop2 {
  always (
   (L1.finalized_state = L1.finalized_state')
     implies
       L1.forced_queue in L1.forced_queue'
  )
}
check cold_rollup_prop2 for 7

assert cold_rollup_prop3 {
  always (
   (L1.forced_queue' = L1.forced_queue and some L1.forced_queue)
     implies
       L1.finalized_state = L1.finalized_state'
  )
}
check cold_rollup_prop3 for 5

assert cold_rollup_prop4 {
 always (
   (plus[#L1.finalized_state,1] >= #L1.finalized_state')
 )
}
check cold_rollup_prop4

// forced txs move down in the forced queue
assert cold_rollup_prop5 {
 always (
    (some L1.forced_queue 
    and #L1.finalized_state < #L1.finalized_state') implies
    (all x : Forced |
      (some L1.forced_queue.idxOf[x]
      and some L1.forced_queue'.idxOf[x])
       implies 
        L1.forced_queue'.idxOf[x] < L1.forced_queue.idxOf[x])
 )
}
check cold_rollup_prop5

// if something gets into finilized_state then at some moment there was a proof and a commitment for it
assert finalized_state_correct { 
 always(
   all b : Block | some L1.finalized_state.idxOf[b]
     implies
      (once some c : Commitment , p : Proof | 
         c in L1.commitments 
     and p in L1.proofs 
     and c.diff = p.diff
     and b = c.diff)
 )
}
check finalized_state_correct for 3

run two_process_in_a_row {
  eventually (some rollup_simple_happens and after some rollup_simple_happens)
} for 5

run { 
 eventually (#forced_queue = 2 and #finalized_state = 1 ; #finalized_state = 2)
} for 10 


