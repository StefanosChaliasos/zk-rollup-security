module scroll/scroll_dynamics

open scroll/scroll_data_model

// ========== Basic Rollup Operations ==========

pred receive_commitment[c : Commitment] {
  // No duplicates
  no c & ScrollL1.commitments 
  // Committed state extends currently finalized state
  c.state.subseq[0,sub[#ScrollL1.finalized_state,1]] = ScrollL1.finalized_state 

  // Update state
  ScrollL1.commitments' = ScrollL1.commitments + c

  // Frame conditions - keep everything else unchanged
  ScrollL1.finalized_state' = ScrollL1.finalized_state
  ScrollL1.proofs' = ScrollL1.proofs
  ScrollL1.message_queue' = ScrollL1.message_queue
  ScrollL1.next_unfinalized_index' = ScrollL1.next_unfinalized_index
  ScrollL1.enforced_mode' = ScrollL1.enforced_mode
  ScrollL1.last_finalized_batch_timestamp' = ScrollL1.last_finalized_batch_timestamp
  ScrollL1.max_delay_message_queue' = ScrollL1.max_delay_message_queue
  ScrollL1.max_delay_enter_enforced_mode' = ScrollL1.max_delay_enter_enforced_mode
  ScrollL1.current_timestamp' = ScrollL1.current_timestamp
  
  // Keep all data unchanged
  Address = Address'
  Input = Input'
  Block = Block'
  block_inputs = block_inputs'
  timestamp = timestamp'
  state = state'
  diff = diff'
  EnforcedEvent = EnforcedEvent'
  tx = tx'
  original_sender = original_sender'
  fee_paid = fee_paid'
  QueuedMessage = QueuedMessage'
  enforced_input = enforced_input'
  rolling_hash = rolling_hash'
  enqueue_timestamp = enqueue_timestamp'
}

pred receive_proof[p : Proof] {
  // No duplicates  
  no p & ScrollL1.proofs
  // Proof state extends currently finalized state
  p.state.subseq[0,sub[#ScrollL1.finalized_state,1]] = ScrollL1.finalized_state 

  // Update state
  ScrollL1.proofs' = ScrollL1.proofs + p

  // Frame conditions
  ScrollL1.finalized_state' = ScrollL1.finalized_state
  ScrollL1.commitments' = ScrollL1.commitments
  ScrollL1.message_queue' = ScrollL1.message_queue
  ScrollL1.next_unfinalized_index' = ScrollL1.next_unfinalized_index
  ScrollL1.enforced_mode' = ScrollL1.enforced_mode
  ScrollL1.last_finalized_batch_timestamp' = ScrollL1.last_finalized_batch_timestamp
  ScrollL1.max_delay_message_queue' = ScrollL1.max_delay_message_queue
  ScrollL1.max_delay_enter_enforced_mode' = ScrollL1.max_delay_enter_enforced_mode
  ScrollL1.current_timestamp' = ScrollL1.current_timestamp

  // Keep all data unchanged
  Address = Address'
  Input = Input'
  Block = Block'
  block_inputs = block_inputs'
  timestamp = timestamp'
  state = state'
  diff = diff'
  EnforcedEvent = EnforcedEvent'
  tx = tx'
  original_sender = original_sender'
  fee_paid = fee_paid'
  QueuedMessage = QueuedMessage'
  enforced_input = enforced_input'
  rolling_hash = rolling_hash'
  enqueue_timestamp = enqueue_timestamp'
}

// ========== Enforced Transaction Operations ==========

pred submit_enforced_transaction[ei : EnforcedInput] {
  // Create new queued message
  some qm : QueuedMessage | {
    qm.enforced_input = ei
    qm.enqueue_timestamp = ScrollL1.current_timestamp
    
    // Calculate rolling hash (simplified - use abstract hash function)
    (#ScrollL1.message_queue > 0) implies {
      // Hash = hash(previous_hash, current_transaction) 
      // Abstract: combine previous hash with current transaction using simple arithmetic
      qm.rolling_hash = ScrollL1.message_queue.last.rolling_hash.plus[#ei.tx]
    } else {
      // First message uses transaction object as initial hash seed
      qm.rolling_hash = #ei.tx
    }
    
    // Add to queue
    ScrollL1.message_queue' = ScrollL1.message_queue.add[qm]
  }
  
  // Fee validation (abstracted - just ensure fee was paid)
  ei.fee_paid > 0

  // Frame conditions  
  ScrollL1.finalized_state' = ScrollL1.finalized_state
  ScrollL1.commitments' = ScrollL1.commitments
  ScrollL1.proofs' = ScrollL1.proofs
  ScrollL1.next_unfinalized_index' = ScrollL1.next_unfinalized_index
  ScrollL1.enforced_mode' = ScrollL1.enforced_mode
  ScrollL1.last_finalized_batch_timestamp' = ScrollL1.last_finalized_batch_timestamp
  ScrollL1.max_delay_message_queue' = ScrollL1.max_delay_message_queue
  ScrollL1.max_delay_enter_enforced_mode' = ScrollL1.max_delay_enter_enforced_mode
  ScrollL1.current_timestamp' = ScrollL1.current_timestamp

  // Keep other data unchanged
  Address = Address'
  Input = Input'
  Block = Block'
  block_inputs = block_inputs'
  timestamp = timestamp'
  state = state'
  diff = diff'
  EnforcedEvent = EnforcedEvent'
  tx = tx'
  original_sender = original_sender'
  fee_paid = fee_paid'
  enforced_input = enforced_input'
  rolling_hash = rolling_hash'
  enqueue_timestamp = enqueue_timestamp'
}

// ========== Batch Processing Operations ==========

pred normal_batch_commit[c: Commitment, p: Proof] {
  // Normal mode only (sequencer controlled)
  ScrollL1.enforced_mode = False
  
  // Standard commitment/proof matching
  c in ScrollL1.commitments  
  p in ScrollL1.proofs
  c.state = p.state
  c.diff = p.diff
  c.state = ScrollL1.finalized_state
  
  // Ensure no duplicate processing
  no ScrollL1.finalized_state.idxOf[c.diff]
  
  // Must include enforced transactions if they have timed out
  // In normal mode, sequencer can choose to skip enforced messages until timeout
  (#unfinalized_messages > 0 and 
   ScrollL1.current_timestamp.minus[oldest_unfinalized_timestamp] > ScrollL1.max_delay_message_queue) implies {
    // First unfinalized message must be included if it has timed out
    unfinalized_messages.first.enforced_input.tx in c.diff.block_inputs.elems
  }
  
  // Update finalized state
  ScrollL1.finalized_state' = ScrollL1.finalized_state.add[p.diff]
  ScrollL1.last_finalized_batch_timestamp' = ScrollL1.current_timestamp
  
  // Remove processed commitments and proofs
  ScrollL1.proofs' = ScrollL1.proofs - (p + { q : Proof | #q.state < #ScrollL1.finalized_state' })
  ScrollL1.commitments' = ScrollL1.commitments - (c + { q : Commitment | #q.state < #ScrollL1.finalized_state' })
  
  // Update unfinalized index based on processed messages
  // Count how many enforced messages were processed in this batch
  let processed_enforced = { qm : QueuedMessage | 
    qm in unfinalized_messages.elems and qm.enforced_input.tx in c.diff.block_inputs.elems } | {
    ScrollL1.next_unfinalized_index' = ScrollL1.next_unfinalized_index.plus[#processed_enforced]
  }

  // Frame conditions
  ScrollL1.message_queue' = ScrollL1.message_queue
  ScrollL1.enforced_mode' = ScrollL1.enforced_mode
  ScrollL1.max_delay_message_queue' = ScrollL1.max_delay_message_queue
  ScrollL1.max_delay_enter_enforced_mode' = ScrollL1.max_delay_enter_enforced_mode
  ScrollL1.current_timestamp' = ScrollL1.current_timestamp

  // Keep data unchanged
  Address = Address'
  Input = Input'
  Block = Block'
  block_inputs = block_inputs'
  timestamp = timestamp'
  state = state'
  diff = diff'
  EnforcedEvent = EnforcedEvent'
  tx = tx'
  original_sender = original_sender'
  fee_paid = fee_paid'
  QueuedMessage = QueuedMessage'
  enforced_input = enforced_input'
  rolling_hash = rolling_hash'
  enqueue_timestamp = enqueue_timestamp'
}

pred enter_enforced_mode {
  // Can only enter enforced mode if conditions are met
  should_enter_enforced_mode
  ScrollL1.enforced_mode = False
  
  // Enter enforced mode
  ScrollL1.enforced_mode' = True
  
  // Revert any uncommitted batches (simplified - remove unmatched commitments/proofs)
  ScrollL1.commitments' = { c : Commitment | c in ScrollL1.commitments and #c.state <= #ScrollL1.finalized_state }
  ScrollL1.proofs' = { p : Proof | p in ScrollL1.proofs and #p.state <= #ScrollL1.finalized_state }

  // Frame conditions
  ScrollL1.finalized_state' = ScrollL1.finalized_state
  ScrollL1.message_queue' = ScrollL1.message_queue
  ScrollL1.next_unfinalized_index' = ScrollL1.next_unfinalized_index
  ScrollL1.last_finalized_batch_timestamp' = ScrollL1.last_finalized_batch_timestamp
  ScrollL1.max_delay_message_queue' = ScrollL1.max_delay_message_queue
  ScrollL1.max_delay_enter_enforced_mode' = ScrollL1.max_delay_enter_enforced_mode
  ScrollL1.current_timestamp' = ScrollL1.current_timestamp

  // Keep data unchanged
  Address = Address'
  Input = Input'
  Block = Block'
  block_inputs = block_inputs'
  timestamp = timestamp'
  state = state'
  diff = diff'
  EnforcedEvent = EnforcedEvent'  
  tx = tx'
  original_sender = original_sender'
  fee_paid = fee_paid'
  QueuedMessage = QueuedMessage'
  enforced_input = enforced_input'
  rolling_hash = rolling_hash'
  enqueue_timestamp = enqueue_timestamp'
}

pred enforced_batch_commit_and_finalize {
  // Must be in enforced mode with pending messages
  can_process_enforced_batch
  
  // Create and immediately finalize batch with all pending enforced transactions
  some b : Block | {
    // Include all unfinalized enforced transactions
    b.block_inputs = unfinalized_messages.enforced_input.tx
    b.timestamp = ScrollL1.current_timestamp
    
    // Add to finalized state
    ScrollL1.finalized_state' = ScrollL1.finalized_state.add[b]
    ScrollL1.last_finalized_batch_timestamp' = ScrollL1.current_timestamp
    
    // Mark all messages as finalized
    ScrollL1.next_unfinalized_index' = #ScrollL1.message_queue
  }
  
  // Exit enforced mode after processing
  ScrollL1.enforced_mode' = False

  // Frame conditions  
  ScrollL1.message_queue' = ScrollL1.message_queue
  ScrollL1.commitments' = ScrollL1.commitments
  ScrollL1.proofs' = ScrollL1.proofs
  ScrollL1.max_delay_message_queue' = ScrollL1.max_delay_message_queue
  ScrollL1.max_delay_enter_enforced_mode' = ScrollL1.max_delay_enter_enforced_mode
  ScrollL1.current_timestamp' = ScrollL1.current_timestamp

  // Keep data unchanged
  Address = Address'
  Input = Input'
  Block = Block'
  block_inputs = block_inputs'
  timestamp = timestamp'
  state = state'
  diff = diff'
  EnforcedEvent = EnforcedEvent'
  tx = tx'
  original_sender = original_sender'
  fee_paid = fee_paid'
  QueuedMessage = QueuedMessage'
  enforced_input = enforced_input'
  rolling_hash = rolling_hash'
  enqueue_timestamp = enqueue_timestamp'
}

// ========== Time Progression ==========

pred advance_time {
  ScrollL1.current_timestamp' = ScrollL1.current_timestamp.plus[1]
  
  // Frame conditions - everything else unchanged
  ScrollL1.finalized_state' = ScrollL1.finalized_state
  ScrollL1.commitments' = ScrollL1.commitments
  ScrollL1.proofs' = ScrollL1.proofs
  ScrollL1.message_queue' = ScrollL1.message_queue
  ScrollL1.next_unfinalized_index' = ScrollL1.next_unfinalized_index
  ScrollL1.enforced_mode' = ScrollL1.enforced_mode
  ScrollL1.last_finalized_batch_timestamp' = ScrollL1.last_finalized_batch_timestamp
  ScrollL1.max_delay_message_queue' = ScrollL1.max_delay_message_queue
  ScrollL1.max_delay_enter_enforced_mode' = ScrollL1.max_delay_enter_enforced_mode

  // Keep all data unchanged
  Address = Address'
  Input = Input'
  Block = Block'
  block_inputs = block_inputs'
  timestamp = timestamp'
  state = state'
  diff = diff'
  EnforcedEvent = EnforcedEvent'
  tx = tx'
  original_sender = original_sender'
  fee_paid = fee_paid'
  QueuedMessage = QueuedMessage'
  enforced_input = enforced_input'
  rolling_hash = rolling_hash'
  enqueue_timestamp = enqueue_timestamp'
}

// ========== Stutter ==========

pred stutter {
  // Keep all ScrollL1 state unchanged
  ScrollL1.finalized_state' = ScrollL1.finalized_state
  ScrollL1.commitments' = ScrollL1.commitments
  ScrollL1.proofs' = ScrollL1.proofs
  ScrollL1.message_queue' = ScrollL1.message_queue
  ScrollL1.next_unfinalized_index' = ScrollL1.next_unfinalized_index
  ScrollL1.enforced_mode' = ScrollL1.enforced_mode
  ScrollL1.last_finalized_batch_timestamp' = ScrollL1.last_finalized_batch_timestamp
  ScrollL1.max_delay_message_queue' = ScrollL1.max_delay_message_queue
  ScrollL1.max_delay_enter_enforced_mode' = ScrollL1.max_delay_enter_enforced_mode
  ScrollL1.current_timestamp' = ScrollL1.current_timestamp

  // Keep all data unchanged
  Address = Address'
  Input = Input'
  Block = Block'
  block_inputs = block_inputs'
  timestamp = timestamp'
  state = state'
  diff = diff'
  EnforcedEvent = EnforcedEvent'
  tx = tx'
  original_sender = original_sender'
  fee_paid = fee_paid'
  QueuedMessage = QueuedMessage'
  enforced_input = enforced_input'
  rolling_hash = rolling_hash'
  enqueue_timestamp = enqueue_timestamp'
}

// ========== System Specifications ==========

fact {
  // Start with empty system
  no ScrollL1.finalized_state
  no ScrollL1.commitments  
  no ScrollL1.proofs
  no ScrollL1.message_queue
  ScrollL1.next_unfinalized_index = 0
  ScrollL1.enforced_mode = False
  ScrollL1.last_finalized_batch_timestamp = 0
  ScrollL1.current_timestamp = 0
  ScrollL1.max_delay_message_queue = 3  // Example timeout values
  ScrollL1.max_delay_enter_enforced_mode = 5
}

// Event names (following original pattern)
enum Event { 
  Stutter,

  ReceiveComm, 
  ReceiveProof, 
  ProcessNormal,

  SubmitEnforced,
  EnterEnforcedMode,
  ProcessEnforced,

  AdvanceTime
}

// Event detection functions (following original pattern)
fun stutter_happens : set Event {
  { e: Stutter | stutter }
}

fun receive_commitment_happens : Event -> Commitment {
  { e : ReceiveComm, c: Commitment | receive_commitment[c] }
}

fun receive_proof_happens : Event -> Proof {
  { e : ReceiveProof, p: Proof | receive_proof[p] }
}

fun submit_enforced_tx_happens : Event -> EnforcedInput {
  { e : SubmitEnforced, ei: EnforcedInput | submit_enforced_transaction[ei] }
}

fun normal_batch_commit_happens : Event {
  { e : ProcessNormal | some c : Commitment, p : Proof | normal_batch_commit[c, p] }
}

fun enter_enforced_mode_happens : set Event {
  { e : EnterEnforcedMode | enter_enforced_mode }
}

fun enforced_batch_commit_happens : set Event {
  { e : ProcessEnforced | enforced_batch_commit_and_finalize }
}

fun advance_time_happens : set Event {
  { e : AdvanceTime | advance_time }
}

// Function that returns the set of events currently happening (following original pattern)
fun events : set Event {
  // simple
  stutter_happens +
  receive_commitment_happens.Commitment +
  receive_proof_happens.Proof +

  // forced
  submit_enforced_tx_happens.EnforcedInput +
  normal_batch_commit_happens +
  enter_enforced_mode_happens +
  enforced_batch_commit_happens +
  advance_time_happens
}

// ========== System Specifications ==========

// Simple Scroll specification - no enforced transactions, normal rollup only
pred spec_scroll_simple {
  // No enforced transactions or enforced mode
  always (no ScrollL1.message_queue and no EnforcedInput and ScrollL1.enforced_mode = False)
  // Only allow basic rollup events (exclude enforced transaction events)
  always some (events - SubmitEnforced - EnterEnforcedMode - ProcessEnforced)
}

// Full Scroll specification - includes enforced transaction queue mechanism  
pred spec_scroll_forced {
  always some events
}

// Complete system specification (alias for backward compatibility)
pred scroll_system {
  spec_scroll_forced
}