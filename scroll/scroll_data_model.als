module scroll/scroll_data_model

// Boolean implementation as per https://alloy.readthedocs.io/en/latest/modules/boolean.html
abstract sig Bool {}
one sig True, False extends Bool {}

// Addresses represent Ethereum addresses
// We distinguish between EOAs and contracts for aliasing logic
var abstract sig Address {}
var sig EOA extends Address {}
var sig Contract extends Address {}

// Inputs represent transactions submitted by users
var sig Input {}

// Blocks encapsulate sequences of inputs with additional metadata
var sig Block {
  var block_inputs : seq Input,
  var timestamp : one Int
}

// ZK Objects for commitments and proofs
var abstract sig ZKObject {
  var state : seq Block,
  var diff : one Block 
}

var sig Proof extends ZKObject {}{
  not state.hasDups
  diff not in state.elems
}

var sig Commitment extends ZKObject {}{
  not state.hasDups
  diff not in state.elems
}

// Scroll-specific: Enforced transactions that can be forced through L1
var abstract sig EnforcedEvent {}

// Users can force their transactions through the EnforcedTxGateway
var sig EnforcedInput extends EnforcedEvent {
  var tx : one Input,
  var original_sender : one Address,  // sender before aliasing
  var fee_paid : one Int              // abstract fee representation
}

// Message queue entry with rolling hash and timestamp
// We use a FIFO queue, so message_index is implicit from queue position
var sig QueuedMessage {
  var enforced_input : one EnforcedInput,
  var rolling_hash : one Int,         // simplified hash representation
  var enqueue_timestamp : one Int
}

// L1 state representing Scroll's rollup contracts
one sig ScrollL1 {
  // Basic rollup state
  var finalized_state : seq Block,
  var commitments : set Commitment,
  var proofs : set Proof,
  
  // Scroll-specific message queue (L1MessageQueueV2)
  var message_queue : seq QueuedMessage,
  var next_unfinalized_index : one Int,
  
  // Enforced mode state
  var enforced_mode : one Bool,
  var last_finalized_batch_timestamp : one Int,
  
  // System configuration (abstracted)
  var max_delay_message_queue : one Int,
  var max_delay_enter_enforced_mode : one Int,
  var current_timestamp : one Int
} {
  not finalized_state.hasDups
  not message_queue.hasDups
  // Invariants
  next_unfinalized_index >= 0
  next_unfinalized_index <= #message_queue
}

// Address aliasing helper - simplified version of AddressAliasHelper
fun apply_l1_to_l2_alias[addr : Address] : Address {
  addr in Contract implies addr else addr  // Abstract: contracts get aliased, EOAs don't
}

// Helper functions
fun all_finalized_inputs : set Input {
  { i : Input | i in ScrollL1.finalized_state.elems.block_inputs.elems } 
}

fun new_finalized_inputs : set Input {
  ScrollL1.finalized_state'.elems.block_inputs.elems 
      - ScrollL1.finalized_state.elems.block_inputs.elems
}

fun unfinalized_messages : seq QueuedMessage {
  ScrollL1.message_queue.subseq[ScrollL1.next_unfinalized_index, sub[#ScrollL1.message_queue, 1]]
}

fun oldest_unfinalized_timestamp : Int {
  #unfinalized_messages > 0 implies unfinalized_messages.first.enqueue_timestamp else 0
}

// Predicates for enforced mode conditions
pred should_enter_enforced_mode {
  // Condition 1: oldest unfinalized message exceeds delay threshold
  (#unfinalized_messages > 0 and 
   ScrollL1.current_timestamp.minus[oldest_unfinalized_timestamp] > ScrollL1.max_delay_message_queue)
  or
  // Condition 2: last finalized batch exceeds delay threshold  
  (ScrollL1.current_timestamp.minus[ScrollL1.last_finalized_batch_timestamp] > ScrollL1.max_delay_enter_enforced_mode)
}

pred can_process_enforced_batch {
  ScrollL1.enforced_mode = True and #unfinalized_messages > 0
}