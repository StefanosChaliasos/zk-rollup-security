module alloy/rollup_data_model

// Inputs represent transactions submitted by the user
// for our use cases we can treat inputs as blackboxes
var sig Input {}

// Blocks encapsulate sequences of inputs
var sig Block {
  var block_inputs : seq Input
}

// ZK Objects 
// Commitment (a.k.a soft receipt) is usually produced by FastVM and submitted to L1
// Proof is usually produced by slowVM much later than commitment and then sent to L1 for finalization
var abstract sig ZKObject {
  var state : seq Block,
  var diff : one Block 
}
var sig Proof extends ZKObject{}{
  not state.hasDups
  diff not in state.elems
}
var sig Commitment extends ZKObject{}{
  not state.hasDups
  diff not in state.elems
}

// For our rollup model we want L2 events which could be forced through L1
var abstract sig ForcedEvent {}

// Users can force their inputs by submitting a ForcedInput query
var sig ForcedInput extends ForcedEvent {
   var tx : one Input
}
// Some designated actors can update the blacklisting policy through the forced queue
var sig ForcedBlacklistPolicy extends ForcedEvent {
   var predicate : set Input
}

// to start the upgradeability process the upgrade announcement has to be created and submitted
var abstract sig UpgradeAnnouncement {}
// one example of upgradeability announcement is update of the blacklist
var sig BlacklistUpdateAnnouncement extends UpgradeAnnouncement {
  var blacklist_policy : one ForcedBlacklistPolicy
}
// after announcement users get a period of time to act on the "upgrade announcement". The end of this
// period is signalled by the timeout event
var sig Timeout {
  var upgrade : one UpgradeAnnouncement
}


// L1 state of the rollup
one sig L1 {
  // simple rollup model
  var finalized_state : seq Block,
  var commitments : set Commitment,
  var proofs : set Proof,
  // forced queue
  var forced_queue : seq ForcedEvent,
  // eager blacklists 
  var blacklist : set Input,
  // generic upgradeability
  var ongoing_upgrade : lone UpgradeAnnouncement
}{ 
  not finalized_state.hasDups
  not forced_queue.hasDups
}



// HELPERS
fun all_finalized_inputs : set Input {
  { i : Input | i in L1.finalized_state.elems.block_inputs.elems } 
}

fun new_finalized_inputs : set Input {
  L1.finalized_state'.elems.block_inputs.elems 
      - L1.finalized_state.elems.block_inputs.elems
}

pred upgrade_in_progress {
  some L1.ongoing_upgrade
}

pred upgrade_queueing {
  upgrade_in_progress and (all t : Timeout | not (t.upgrade = L1.ongoing_upgrade))
}
pred upgrade_queueing_finished {
  upgrade_in_progress and some t : Timeout | t.upgrade = L1.ongoing_upgrade
}

pred upgrade_forced_queue_processing {
  upgrade_queueing_finished and some L1.forced_queue
}

pred upgrade_forced_queue_processing_finished {
  upgrade_queueing_finished and no L1.forced_queue
}
