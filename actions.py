from types import NoneType
Receipt = NoneType
Proof = NoneType

Address = User | Contract
Origin = L1 | L2
Tx = (from_adrr, to_addr, value, origin)
Mempool = Set[Tx]
L2_State = (Map[Address,Balance],Storage)
L2_State_Status = Confirmation | 

def l2_tx(from_addr, to_addr, value):
    """
    Initiates a transaction on the L2 network and waits for a receipt confirming the transaction has been processed.    
    """

def sequence_l2_txs(mempool, l2_state) -> Receipt:
    """
    Reads the L2 mempool, orders transactions, executes them, and creates a block. 
    Returns receipts to users and calls the aggregator.

    Component: Sequencer
    Sends message to: Aggregator
    Processed by: batch_blocks
    Waits for: -
    Publish: Blocks in L2
    Returns to: L2 User
    """

def batch_blocks(l2_state):
    """
    Processes blocks in order and batches them together. 
    Sends the batch to the relayer and requests a proof from the prover.
    Submits the proof to the relayer.

    Component: Aggregator
    Sends message to: Relayer, Prover
    Processed by: relay_commitment, prove_batch, relay_proof
    Waits for: prove_batch
    Publish: -
    Returns to: -
    """

def prove_batch(batch) -> Proof:
    """
    Proves a batch of transactions.

    Component: Prover
    Sends message to: -
    Processed by: -
    Waits for: -
    Publish: -
    Returns to: Aggregator
    """

def relay_commitment(batch_data):
    """
    Receives a batch and invokes the rollup contract on L1 to commit the batch.

    Component: Relayer
    Sends message to: L1 Rollup Contract
    Processed by: l1_commit
    Waits for: -
    Publish: -
    Returns to: -
    """

def relay_proof(batch_data, proof):
    """
    Receives a proof for a batch and invokes the rollup contract on L1 to verify the proof.

    Component: Relayer
    Sends message to: L1 Rollup Contract
    Processed by: l1_verify
    Waits for: -
    Publish: -
    Returns to: -
    """

def l1_commit(batch_data):
    """
    Receives a batch and stores it in the state of L1.

    Component: L1 Rollup Contract
    Sends message to: -
    Processed by: -
    Waits for: -
    Publish: Batch Commitment to L1
    Returns to: -
    """

def l1_verify(batch_data, proof):
    """
    Receives a proof, stores it in the state of L1, and verifies it.

    Component: L1 Rollup Contract
    Sends message to: -
    Processed by: -
    Waits for: -
    Publish: Proof of the batch and verification status to L1
    Returns to: -
    """

def l1_deposit_bridge_tx(from_addr, to_addr, value, fees, gas_price, calldata) -> Receipt:
    """
    Initiates a transaction on the L1 network and waits for a receipt confirming the transaction has been processed by the bridge contract in L1.

    Component: L1 user
    Sends message to: L1 bridge contract
    Processed by: process_l1_bridge_tx
    Waits for: -
    Publish: -
    Returns to: -
    """

def process_l1_bridge_tx(from_addr, to_addr, value):
    """
    Process a bridge transaction and update the L1's bridge state.

    Component: L1 bridge contract
    Sends message to: Relayer
    Processed by: l1_to_l2_bridge_relay
    Waits for: -
    Publish: -
    Returns to: -
    """

def l1_to_l2_bridge_relay(from_addr, to_addr, value):
    """
    Process messages for the bridge contract in L1 and update the L2 bridge contract.

    Component: Relayer
    Sends message to: L2 mempool
    Processed by: sequence_l2_txs
    Waits for: -
    Publish: -
    Returns to: -
    """

def l2_withdraw_bridge_tx(from_addr, to_addr, value) -> Receipt:
    """
    Initiates a transaction on the L2 network and waits for a receipt confirming the transaction has been processed by the bridge contract in L2.

    Component: L2 user
    Sends message to: L2 bridge contract
    Processed by: sequence_l2_txs
    Waits for: -
    Publish: -
    Returns to: -
    """

def l1_withdraw_bridge_tx(from_addr, to_addr, value) -> Receipt:
    """
    Initiates a transaction on the L1 network and waits for a receipt confirming the transaction has been processed by the bridge contract in L1. 
    This will only succeed if the l2 tx has been finilized.

    Component: L1 user
    Sends message to: L1 bridge contract
    Processed by: -
    Waits for: -
    Publish: -
    Returns to: -
    """

def l1_force_tx(from_addr, to_addr, value, fees, gas_price, calldata) -> Receipt:
    """
    Initiates a transaction on the L1 network and waits for a receipt confirming the transaction has been processed by the rollup contract in L1. 

    Component: L1 user
    Sends message to: L1 rollup contract
    Processed by: l1_process_force_tx
    Waits for: -
    Publish: -
    Returns to: -
    """

def l1_process_force_tx(from_addr, to_addr, value, fees, gas_price, calldata):
    """
    Process a force transaction and keep track of it.

    Component: L1 rollup contract
    Sends message to: Relayer
    Processed by: relay_force_tx
    Waits for: -
    Publish: -
    Returns to: -
    """

def relay_force_tx(tx):
    """
    Add the force_tx in the force txs mempool

    Component: Relayer
    Sends message to: L2 force txs mempool
    Processed by: sequence_l2_txs
    Waits for: -
    Publish: -
    Returns to: -
    """
