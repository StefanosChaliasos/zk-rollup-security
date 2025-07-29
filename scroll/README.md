# Scroll Rollup Alloy Model

This directory contains an Alloy model specifically designed to capture the security properties and behavior of the Scroll ZK-rollup implementation, focusing on the enforced transaction queue mechanism that provides censorship resistance.

| NOTE: Scroll only supports forced queue (priority queue) at the moment, and it doesn't support safe upgradeability or blacklisting.

## Overview

The Scroll model adapts the generic ZK-rollup framework to model Scroll's specific implementation details:

- **EnforcedTxGateway**: Transaction submission 
- **L1MessageQueueV2**: Sequential message queue with rolling hash integrity  
- **ScrollChain**: Dual-mode operation (normal vs enforced)
- **Censorship Resistance**: Timeout-based enforced mode activation

Unlike the generic model, Scroll does not implement blacklisting or upgradeability mechanisms, allowing for a simpler but still robust design focused on liveness guarantees.

The core difference with the forced queue is that Scroll can progress without processing transactions from the forced queue as long as those transactions have not reached a maximum time until processed (timeout).

## Alloy Formal Model Design

### Data Model (`scroll_data_model.als`)

The Alloy model abstracts Scroll's implementation into essential components:

```alloy
// Core State
var sig ScrollL1 {
  var finalized_state : seq Block,
  var commitments : set Commitment,
  var proofs : set Proof,
  var message_queue : seq QueuedMessage,
  var next_unfinalized_index : one Int,
  var enforced_mode : one Bool,
  var current_timestamp : one Int,
  var max_delay_message_queue : one Int
}
```

**Design Decisions:**
- **Sequences for State**: `finalized_state` as sequence captures ordering
- **Sets for ZK Objects**: Commitments/proofs don't need ordering
- **Message Queue**: FIFO queue with rolling hashes and timestamps
- **Simplified Types**: `Int` for hashes/timestamps, `Bool` for flags

### Dynamics (`scroll_dynamics.als`)

The dynamics model captures valid state transitions:

```alloy
// Valid operations
enum Event {
  submit_batch,        // Sequencer commits batch
  finalize_batch,      // Prover finalizes with ZK proof
  forced_commit,       // Enforced mode batch processing
  queue_message,       // Add enforced transaction
  time_tick           // Time advancement
}
```

**Key Predicates:**
- `normal_batch_commit`: Standard sequencer flow
- `normal_batch_finalize`: Proof verification and finalization
- `forced_batch_commit`: Censorship resistance processing
- `should_enter_enforced_mode`: Timeout condition check

## Property Categories

### 1. Simple Rollup Properties (SRP)

These verify basic rollup integrity:

#### SRP1: Event Granularity
```alloy
pred srp1 {
  always lone events  // At most one event at a time
}
```
**Purpose**: Ensures atomic state transitions

#### SRP2: Monotonic State
```alloy
pred srp2 { 
  always (ScrollL1.finalized_state in ScrollL1.finalized_state')
}
```
**Purpose**: Finalized state only grows (no rollbacks)

#### SRP3: Justified State
```alloy
pred srp3 { 
  always(
    all b : Block | some ScrollL1.finalized_state.idxOf[b]
      implies (once some c : Commitment, p : Proof | justified(c,p,b))
           or (once enforced_mode_processing)
  )
}
```
**Purpose**: Every finalized block has proper justification

#### SRP4: State Progression Validity
```alloy
pred srp4 { 
  always(
    all c : Commitment, p : Proof | 
      #c.state < #ScrollL1.finalized_state
      implies not normal_batch_commit[c,p]
  )
}
```
**Purpose**: Cannot process old states

### 2. Forced Queue Properties (FQP)

These verify censorship resistance:

#### FQP1: Timeout-Guaranteed Processing
```alloy
pred fqp1 {
  always (
    (messages_exist and state_advances and timeout_exceeded)
    implies messages_processed
  )
}
```
**Purpose**: Core censorship resistance - timed out messages must be processed (different that the original FQP1)

#### FQP2: Message Queue Stable
```alloy
pred fqp2 {
  always (
    (ScrollL1.finalized_state = ScrollL1.finalized_state')
    implies (queue_only_grows and unfinalized_index_stable)
  )
}
```
**Purpose**: Queue integrity when state unchanged

#### FQP3: State Invariant
```alloy
pred fqp3 {
  always (
    (unfinalized_messages_exist and queue_unchanged and timeout_exceeded)
    implies state_unchanged
  )
}
```
**Purpose**: Cannot advance state while ignoring timed-out messages

#### FQP4: Queued Message Progress
```alloy
pred fqp4 {
  always (
    (state_advances and unfinalized_messages_exist)
    implies next_unfinalized_index_monotonic
  )
}
```
**Purpose**: Message processing progress is monotonic

#### FQP5: Order Preservation
```alloy
pred fqp5 {
  always (
    all qm1, qm2 : QueuedMessage |
      (qm1 before qm2 in queue) implies
        (qm2 processed implies qm1 processed)
  )
}
```
**Purpose**: FIFO message processing order

#### FQP6: Finalization Confirmation
```alloy
pred fqp6 {
  always (
    all qm : QueuedMessage | 
      (qm was_unfinalized and qm not_unfinalized_now)
      implies qm finalized
  )
}
```
**Purpose**: Proper state transitions for messages

### 3. Scroll-Specific Properties (SP)

These verify implementation-specific mechanisms:

#### SP1: Rolling Hash Integrity
```alloy
pred sp1 {
  always (
    all qm : QueuedMessage |
      qm.rolling_hash = compute_rolling_hash(prev_hash, qm.tx)
  )
}
```
**Purpose**: Cryptographic message chain integrity

#### SP2: Enforced Mode Activation
```alloy
pred sp2 {
  always (
    (enforced_mode_activated)
    implies timeout_conditions_met
  )
}
```
**Purpose**: Mode transitions only on valid conditions

#### SP3: Mode Consistency
```alloy
pred sp3 {
  always (
    (enforced_mode = True)
    implies no_normal_operations
  )
}
```
**Purpose**: Mode isolation and mutual exclusivity

#### SP4: Fee Payment
```alloy
pred sp4 {
  always (
    all enforced_tx : EnforcedInput |
      enforced_tx.fee_paid > 0
  )
}
```
**Purpose**: Economic incentive enforcement