module alloy/rollup_data_model

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
/*
L1 : not reflected in VM, commitments, proofs, and finalized_state
*/

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
