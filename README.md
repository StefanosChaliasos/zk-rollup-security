# Specification for the Security of zk-Rollups.

* actions: `actions.py`
* diagram: <https://app.diagrams.net/#G15bRF-NHLI_6j3R8ZZ68vIaE8yW2kQNJT>

## Scenarios

### L2 transaction

1. L2 user: `l2_tx`
2. Sequencer: `sequence_l2_txs`
3. Aggregator: `batch_blocks`
4. (a) Relayer: `relay_commitment`, (b) Prover: `prove_batch`
5. L1 rollup contract: `l1_commit`
6. Relayer: `relay_proof`
7. L2 rollup contract: `l1_verify`

### L1 bridge to L2 (deposit)

1. L1 user: `l1_deposit_bridge_tx`
2. L1 bridge contract: `process_l1_bridge_tx`
3. Relayer: `l1_to_l2_bridge_relay`
4. Steps 2-7 from L2 transaction

### L2 bridge to L1 (withdraw)

1. L2 user: `l2_to_l1_bridge`
2. Steps 2-7 from L2 transaction
3. L1 user: `l1_withdraw_bridge_tx`

### L1 forced transaction to L2

1. L1 user: `l1_force_tx`
2. L1 rollup contract: `l1_process_force_tx`
3. Relayer: `relay_force_tx`
4. Steps 2-7 from L2 transaction
