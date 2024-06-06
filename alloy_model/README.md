# Alloy model for ZK rollups

The model is developed in Alloy 6.1. The properties and testing scenarios are checked with glucose 4.1 SAT solver.

Code accompanying "Towards a formal foundation of blockchain rollups" paper.
 
## Contents

* `rollup_data_model.als` definition of datatypes associated with basic entities of ZK rollups.
   - `Input` abstract inputs (transactions);
   - `Block` encapsulate sequence of inputs;
   - `Proof` and `Commitment` represent proofs and commitments submitted from L2 to L1 for block finalization;
   - `ForcedEvent` events forced upon L2 through L1;
   - `UpgradeAnnouncement` abstract datatype which represents an announcement of an upgrade;
   - `Timeout`  after upgrade announcement users get a period of time to act on the "upgrade announcement". The end of this period is signalled by the timeout event.
   - `L1` a singleton object with fields which represent the state of L2 rollup on L1;
* `rollup_dynamics.als` implementation of queries associated with ZK-rollups.
   - `receive_commitment` receives a commitment for later process.
   - `receive_proof` receives a proof for later process.
   - `receive_forced` receives a forced event, appends it to the queue unless upgrade is in the processing mode.
   - `rollup_process` tries to finalize previously received commitment and the proof.
   - `update_blacklist` processes the blacklisting event from the head of the forced queue.
   - `upgrade_init` receives the `UpgradeAnnouncement` and sets the `L1.ongoing_upgrade` field.
   - `upgrade_timeout` receives a timeout indicating that the current queueing phase of the upgrade has finished.
   - `upgrade_deploy` deploys the upgrade once the processing phase has ended (i.e., forced queue is empty).
   - `stutter`  ensures that traces are infinite
   - `events` set of possible events.
* `rollup_properties.als` specification of properties.
   - `simple_rollup_prop*` - properties associated with the basic ("strawnan") rollups;
   - `cold_rollup_prop*` - properties associated with forced queues;
   - `blacklist_prop*` - properties associated with rollups with "eager" blacklists updated through the forced queue;
   - `upgrade_prop*` - properties associated with "soft" blacklists updated through the upgradeability mechanism;
* `rollup_scenarios.als` various scenarios for testing.
