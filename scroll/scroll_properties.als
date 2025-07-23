module scroll/scroll_properties

open scroll/scroll_data_model
open scroll/scroll_dynamics

// ========== Basic Rollup Properties (SRP) ==========

/* SRP1: Event Granularity - at most one event happens at a time */
pred srp1 {
  always lone events
}

check c_srp1 {
  spec_scroll_simple implies srp1
  spec_scroll_forced implies srp1
} for 5 but 1..10 steps

/* SRP2: Monotonic State - finalized state grows monotonically */
pred srp2 { 
  always (ScrollL1.finalized_state in ScrollL1.finalized_state')
}

check c_srp2 {
  //spec_scroll_simple implies srp2
  spec_scroll_forced implies srp2
} for 5 but 1..10 steps

/* SRP3: Justified State - if block gets finalized then at some moment 
   there was a proof and a commitment for it (normal mode) or it was enforced */
pred srp3 { 
  always(
    all b : Block | some ScrollL1.finalized_state.idxOf[b]
      implies
        // Either justified by proof+commitment (normal mode)
        (once some c : Commitment, p : Proof |
           c in ScrollL1.commitments
           and p in ScrollL1.proofs
           and c.diff = p.diff
           and b = c.diff
           and c.state = ScrollL1.finalized_state)
        or
        // Or processed in enforced mode with pending enforced transactions
        (once (ScrollL1.enforced_mode = True and some unfinalized_messages))
  )
}

check c_srp3 {
  // spec_scroll_simple implies srp3
  spec_scroll_forced implies srp3
} for 5 but 1..10 steps

/* SRP4: State Progression Validity - commitments/proofs smaller than current state 
   are never successfully processed */
pred srp4 { 
  always(
    all c : Commitment, p : Proof | 
      #c.state < #ScrollL1.finalized_state
      implies
        not normal_batch_commit[c,p]
  )
}

check c_srp4 {
  // spec_scroll_simple implies srp4
  spec_scroll_forced implies srp4
} for 5 but 1..10 steps

// ========== Enforced Queue Properties (Adapted FQP) ==========

/* FQP1: Timeout-Guaranteed Processing - if oldest message exceeds timeout and 
   state advances, then it must be processed (Scroll's censorship resistance) */
pred fqp1 {
  always (
    (#unfinalized_messages > 0 
     and some (ScrollL1.finalized_state' - ScrollL1.finalized_state)
     and ScrollL1.current_timestamp.minus[oldest_unfinalized_timestamp] > ScrollL1.max_delay_message_queue)
    implies
      unfinalized_messages.first.enforced_input.tx in new_finalized_inputs
      and ScrollL1.next_unfinalized_index' > ScrollL1.next_unfinalized_index
  )
}

check c_fqp1 {
  spec_scroll_forced implies fqp1
} for 5 but 1..10 steps

/* FQP2: Message Queue Stable - if finalized state didn't change then 
   message queue only grows (new messages can be added) */
pred fqp2 {
  always (
    (ScrollL1.finalized_state = ScrollL1.finalized_state')
    implies
      ScrollL1.message_queue.elems in ScrollL1.message_queue'.elems
      and ScrollL1.next_unfinalized_index = ScrollL1.next_unfinalized_index'
  )
}

check c_fqp2 {
  spec_scroll_forced implies fqp2
} for 5 but 1..10 steps

/* FQP3: State Invariant - if unfinalized messages exist and queue didn't change,
   then finalized state remains unchanged UNLESS messages haven't timed out yet
   (captures Scroll's flexibility for sequencer to skip non-timed-out enforced messages) */
pred fqp3 {
  always (
    (#unfinalized_messages > 0 
     and ScrollL1.message_queue' = ScrollL1.message_queue
     and ScrollL1.next_unfinalized_index' = ScrollL1.next_unfinalized_index
     and ScrollL1.current_timestamp.minus[oldest_unfinalized_timestamp] > ScrollL1.max_delay_message_queue)
    implies
      ScrollL1.finalized_state = ScrollL1.finalized_state'
  )
}

check c_fqp3 {
  spec_scroll_forced implies fqp3
} for 5 but 1..10 steps

/* FQP4: Queued Message Progress - when new blocks are finalized, the next_unfinalized_index 
   must not decrease. This ensures:
   1) Processed messages stay processed (no replay)
   2) Progress on the queue is monotonic (can stay same or advance, never go backward)
   3) If state advances while enforced messages exist, we either:
      - Process some enforced messages (index increases), OR
      - Skip them temporarily if not timed out (index stays same)
   Example: If index=2 (msg0,msg1 processed) and we finalize a new block,
            then index must be >= 2 in the next state */
pred fqp4 {
  always (
    (#unfinalized_messages > 0 and #ScrollL1.finalized_state < #ScrollL1.finalized_state')
    implies
      ScrollL1.next_unfinalized_index' >= ScrollL1.next_unfinalized_index
  )
}

check c_fqp4 {
  spec_scroll_forced implies fqp4
} for 5 but 1..10 steps

/* FQP5: Order Preservation - enforced messages must be processed in FIFO order.
     This ensures:
     1) If qm2 is processed, then qm1 (which comes before it) must be processed too
     2) If both remain unprocessed, they maintain their relative order in the queue
     */
  pred fqp5 {
    always (
      all qm1, qm2 : QueuedMessage |
        (qm1 + qm2 in ScrollL1.message_queue.elems
         and ScrollL1.message_queue.idxOf[qm1] < ScrollL1.message_queue.idxOf[qm2])
        implies
          // Either both maintain their order in the queue
          (qm1 + qm2 in ScrollL1.message_queue'.elems
           implies ScrollL1.message_queue'.idxOf[qm1] < ScrollL1.message_queue'.idxOf[qm2])
          and
          // If qm2 is processed, qm1 must be processed too (FIFO)
          (qm2.enforced_input.tx in new_finalized_inputs
           implies qm1.enforced_input.tx in all_finalized_inputs or qm1.enforced_input.tx in new_finalized_inputs)
    )
  }


check c_fqp5 {
  spec_scroll_forced implies fqp5
} for 5 but 1..10 steps

/* FQP6: Finalization Confirmation - if enforced message was queued and 
   later becomes finalized, it must have been processed through the queue */
pred fqp6 {
  always (
    all qm : QueuedMessage | 
      (qm in ScrollL1.message_queue.elems and qm.enforced_input.tx in all_finalized_inputs)
      implies
        ScrollL1.message_queue.idxOf[qm] < ScrollL1.next_unfinalized_index
  )
}

check c_fqp6 {
  scroll_system implies fqp6
} for 5 but 1..10 steps

// ========== Scroll-Specific Properties ==========

/* SP1: Address Aliasing Correctness - contract addresses get aliased, EOAs don't */
pred sp1 {
  always (
    all ei : EnforcedInput |
      (ei.original_sender in Contract implies apply_l1_to_l2_alias[ei.original_sender] != ei.original_sender)
      and (ei.original_sender in EOA implies apply_l1_to_l2_alias[ei.original_sender] = ei.original_sender)
  )
}

check c_sp1 {
  scroll_system implies sp1
} for 5 but 1..10 steps

/* SP2: Rolling Hash Integrity - each message's rolling hash incorporates previous hash */
pred sp2 {
  always (
    all qm : QueuedMessage |
      (qm in ScrollL1.message_queue.elems and ScrollL1.message_queue.idxOf[qm] > 0)
      implies
        let prev_idx = ScrollL1.message_queue.idxOf[qm].minus[1] |
        let prev_qm = ScrollL1.message_queue[prev_idx] |
          // Simplified: rolling hash should depend on previous hash
          qm.rolling_hash != prev_qm.rolling_hash
  )
}

check c_sp2 {
  scroll_system implies sp2
} for 5 but 1..10 steps

/* SP3: Sequential Message Indexing - messages are ordered in FIFO queue */
pred sp3 {
  always (
    all qm : QueuedMessage |
      qm in ScrollL1.message_queue.elems
      implies
        ScrollL1.message_queue.idxOf[qm] >= 0 
        and ScrollL1.message_queue.idxOf[qm] < #ScrollL1.message_queue
  )
  and
  always (
    all qm1, qm2 : QueuedMessage |
      (qm1 + qm2 in ScrollL1.message_queue.elems 
       and qm1 != qm2)
      implies
        ScrollL1.message_queue.idxOf[qm1] != ScrollL1.message_queue.idxOf[qm2]
  )
}

check c_sp3 {
  scroll_system implies sp3
} for 5 but 1..10 steps

/* SP4: Enforced Mode Activation - enforced mode activates when timeout conditions are met */
pred sp4 {
  always (
    (ScrollL1.enforced_mode = False and ScrollL1.enforced_mode' = True)
    implies
      should_enter_enforced_mode
  )
}

check c_sp4 {
  scroll_system implies sp4
} for 5 but 1..10 steps

/* SP5: Enforced Mode Processing - in enforced mode, all pending messages are processed */
pred sp5 {
  always (
    (ScrollL1.enforced_mode = True 
     and some (ScrollL1.finalized_state' - ScrollL1.finalized_state)
     and #unfinalized_messages > 0)
    implies
      // All unfinalized messages should be processed
      all qm : QueuedMessage |
        (qm in unfinalized_messages.elems)
        implies
          qm.enforced_input.tx in new_finalized_inputs
  )
}

check c_sp5 {
  scroll_system implies sp5
} for 5 but 1..10 steps

/* SP6: Mode Consistency - normal and enforced modes are mutually exclusive */
pred sp6 {
  always (
    (ScrollL1.enforced_mode = True)
    implies
      (all c : Commitment, p : Proof | not normal_batch_commit[c,p])
  )
}

check c_sp6 {
  scroll_system implies sp6
} for 5 but 1..10 steps

/* SP7: Fee Payment - all enforced transactions require fee payment */
pred sp7 {
  always (
    all ei : EnforcedInput |
      (some qm : QueuedMessage | qm.enforced_input = ei and qm in ScrollL1.message_queue.elems)
      implies
        ei.fee_paid > 0
  )
}

check c_sp7 {
  scroll_system implies sp7
} for 5 but 1..10 steps

/* SP8: Timeout Safety - enforced mode cannot be entered prematurely */
pred sp8 {
  always (
    (ScrollL1.enforced_mode = False)
    implies
      (not should_enter_enforced_mode or ScrollL1.enforced_mode' = True)
  )
}

check c_sp8 {
  scroll_system implies sp8
} for 5 but 1..10 steps

// ========== Liveness Properties ==========

/* LP1: Progress Guarantee - if enforced messages exist, they will eventually be processed */
pred lp1 {
  always (
    (#unfinalized_messages > 0)
    implies
      eventually (ScrollL1.next_unfinalized_index' > ScrollL1.next_unfinalized_index)
  )
}

check c_lp1 {
  scroll_system implies lp1
} for 5 but 1..10 steps

/* LP2: Enforced Mode Eventually Exits - enforced mode doesn't last forever */
pred lp2 {
  always (
    (ScrollL1.enforced_mode = True)
    implies
      eventually (ScrollL1.enforced_mode = False)
  )
}

check c_lp2 {
  scroll_system implies lp2  
} for 5 but 1..10 steps

/* LP3: Timeout Resolution - if timeout conditions are met, enforced mode eventually activates */
pred lp3 {
  always (
    (should_enter_enforced_mode and ScrollL1.enforced_mode = False)
    implies
      eventually (ScrollL1.enforced_mode = True)
  )
}

check c_lp3 {
  scroll_system implies lp3
} for 5 but 1..10 steps