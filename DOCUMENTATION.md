# ZK-Rollup Security Model: Paper to Implementation Mapping

This document provides a comprehensive mapping between the theoretical framework presented in the paper "Modeling ZK-Rollup Upgradeability and Security" and its Alloy implementation. Each section maps sections, model, and properties to specific code locations with line numbers.

## Table of Contents
1. [Overview](#overview)
2. [Paper Structure to Implementation Mapping](#paper-structure-to-implementation-mapping)
3. [Data Model Mapping](#data-model-mapping)
4. [System Dynamics Mapping](#system-dynamics-mapping)
5. [Properties Mapping](#properties-mapping)
6. [Scenarios and Testing](#scenarios-and-testing)

## Overview

The implementation consists of four main Alloy modules:
- `rollup_data_model.als`: Core data structures 
- `rollup_dynamics.als`: System behavior and transitions 
- `rollup_properties.als`: Security properties and invariants 
- `rollup_scenarios.als`: Test scenarios 

## Paper Structure to Implementation Mapping

> NOTE 1: below we have lines of code in the Alloy source code that includes the relevant implementation. Note that these lines typically include more details (e.g., in Strawman model we will include a forced_queue in the state), but then we are disabling it in the predicate `spec_simple` in `rollup_dynamics.als:412`.
> NOTE 2: each model builds on top of each other.


#### Section 4.2: Strawman ZK Rollup Model 
- **Core Implementation**: `rollup_data_model.als:1-69`
- **Basic dynamics**: `rollup_dynamics.als` -> `receive_commitment`, `receive_proof`, `rollup_process`
- **Specification**: `rollup_dynamics.als:412` (`spec_simple`)
- **Properties**: `rollup_properties.als:8-68`

#### Section 4.3: Forced Queue
- **Data structures**: `rollup_data_model.als:28-34, 60`
- **Queue operations**: `rollup_dynamics.als:61-102` (`receive_forced`)
- **Processing logic**: `rollup_dynamics.als:104-184` (`rollup_process`)
- **Specification**: `rollup_dynamics.als:418` (`spec_forced_queue`)
- **Properties**: `rollup_properties.als:73-165`

#### Section 4.4: Forced Queue with Blacklisting
- **Blacklist data**: `rollup_data_model.als:36-38, 62`
- **Blacklist operations**: `rollup_dynamics.als:212-238` (update_blacklist)
- **Blacklist constraints**: `rollup_dynamics.als:68-76, 120`
- **Specification**: `rollup_dynamics.als:423` (`spec_blacklist_eager`)
- **Properties**: `rollup_properties.als:167-246`

#### Section 4.5: Forced Queue and Upgradeability
- **Upgrade data structures**: `rollup_data_model.als:41-50, 64`
- **Upgrade operations**: 
  - `rollup_dynamics.als:240-265` (upgrade_init)
  - `rollup_dynamics.als:267-292` (upgrade_timeout)
  - `rollup_dynamics.als:294-319` (upgrade_deploy)
- **Specification**: `rollup_dynamics.als:427` (`spec_blacklist_soft`)
- **Properties**: `rollup_properties.als:248-317`

## Data Model Mapping

### Core Entities (Paper Section 4.2, `rollup_data_model.als`)

| Paper Concept | Implementation | Location |
|--------------|----------------|----------|
| Inputs (transactions) | `var sig Input {}` | `rollup_data_model.als:5` |
| Blocks | `var sig Block { var block_inputs : seq Input }` | `rollup_data_model.als:8-10` |
| ZK Objects | `var abstract sig ZKObject` | `rollup_data_model.als:15-18` |
| Proof | `var sig Proof extends ZKObject` | `rollup_data_model.als:19-22` |
| Commitment | `var sig Commitment extends ZKObject` | `rollup_data_model.als:23-26` |
| L1 State | `one sig L1` | `rollup_data_model.als:54-68` |

### Forced Queue Extensions (Paper Section 4.3, `rollup_data_model.als`)

| Paper Concept | Implementation | Location |
|--------------|----------------|----------|
| Forced Events | `var abstract sig ForcedEvent {}` | `rollup_data_model.als:29` |
| Forced Inputs | `var sig ForcedInput extends ForcedEvent` | `rollup_data_model.als:32-34` |
| Forced Queue | `var forced_queue : seq ForcedEvent` | `rollup_data_model.als:60` |

### Blacklisting (Paper Section 4.4, `rollup_data_model.als`)

| Paper Concept | Implementation | Location |
|--------------|----------------|----------|
| Blacklist Policy | `var sig ForcedBlacklistPolicy extends ForcedEvent` | `rollup_data_model.als:36-38` |
| Active Blacklist | `var blacklist : set Input` | `rollup_data_model.als:62` |

### Upgradeability (Paper Section 4.5, `rollup_data_model.als`)

| Paper Concept | Implementation | Location |
|--------------|----------------|----------|
| Upgrade Announcement | `var abstract sig UpgradeAnnouncement {}` | `rollup_data_model.als:41` |
| Blacklist Update | `var sig BlacklistUpdateAnnouncement` | `rollup_data_model.als:43-45` |
| Timeout | `var sig Timeout` | `rollup_data_model.als:48-50` |
| Ongoing Upgrade | `var ongoing_upgrade : lone UpgradeAnnouncement` | `rollup_data_model.als:64` |

### Helper Functions (`rollup_data_model.als:72-100`)

| Function | Purpose | Location |
|----------|---------|----------|
| `all_finalized_inputs` | Get all finalized inputs | `rollup_data_model.als:73-75` |
| `new_finalized_inputs` | Get newly finalized inputs | `rollup_data_model.als:77-80` |
| `upgrade_in_progress` | Check if upgrade is ongoing | `rollup_data_model.als:82-84` |
| `upgrade_queueing` | Check if in queueing phase | `rollup_data_model.als:86-88` |
| `upgrade_forced_queue_processing` | Check if processing queue | `rollup_data_model.als:93-95` |

## System Dynamics Mapping

### Basic Operations (`rollup_dynamics.als`)

| Operation | Paper Reference | Implementation | Location |
|-----------|----------------|----------------|----------|
| Receive Commitment | Section 4.2 | `pred receive_commitment[c : Commitment]` | `rollup_dynamics.als:5-32` |
| Receive Proof | Section 4.2 | `pred receive_proof[p : Proof]` | `rollup_dynamics.als:34-59` |
| Process Rollup | Section 4.2 | `pred rollup_process` | `rollup_dynamics.als:104-106` |
| Simple Rollup | Section 4.2 | `pred rollup_simple[c: Commitment, p:Proof]` | `rollup_dynamics.als:108-184` |

### Forced Queue Operations (`rollup_dynamics.als`)

| Operation | Paper Reference | Implementation | Location |
|-----------|----------------|----------------|----------|
| Receive Forced | Section 4.3 | `pred receive_forced[f : ForcedEvent]` | `rollup_dynamics.als:61-102` |
| Process Head | Section 4.3, FQP1 | Lines within `rollup_simple` | `rollup_dynamics.als:124-128` |

### Blacklisting Operations (`rollup_dynamics.als`)

| Operation | Paper Reference | Implementation | Location |
|-----------|----------------|----------------|----------|
| Update Blacklist | Section 4.4 | `pred update_blacklist[f : ForcedBlacklistPolicy]` | `rollup_dynamics.als:213-238` |
| Blacklist Check | Section 4.4 | Constraint in rollup_simple | `rollup_dynamics.als:120` |
| Queue Filtering | Section 4.4 | Constraint in receive_forced | `rollup_dynamics.als:70-73` |

### Upgrade Operations (`rollup_dynamics.als`)

| Operation | Paper Reference | Implementation | Location |
|-----------|----------------|----------------|----------|
| Initialize Upgrade | Section 4.5 | `pred upgrade_init[f : UpgradeAnnouncement]` | `rollup_dynamics.als:241-265` |
| Timeout | Section 4.5 | `pred upgrade_timeout[t : Timeout]` | `rollup_dynamics.als:268-292` |
| Deploy Upgrade | Section 4.5 | `pred upgrade_deploy` | `rollup_dynamics.als:295-319` |

### Event System (`rollup_dynamics.als:336-409`)

| Component | Purpose | Location |
|-----------|---------|----------|
| Event Enum | All possible events | `rollup_dynamics.als:336-347` |
| Event Mappings | Connect predicates to events | `rollup_dynamics.als:356-391` |
| Events Function | Set of possible events | `rollup_dynamics.als:392-409` |

## Properties Mapping

### Strawman Rollup Properties (SRP)

| Property Name | Description | Implementation | Location |
|--------------|-------------|----------------|----------|
| SRP1 | Event Granularity | `check c_srp1` | `rollup_properties.als:8-13` |
| SRP2 | Monotonic State | `pred srp2` | `rollup_properties.als:40-48` |
| SRP3 | Justified State | `pred srp3` | `rollup_properties.als:19-36` |
| SRP4 | State Progression Validity | `pred srp4` | `rollup_properties.als:53-67` |

### Forced Queue Properties (FQP)

| Property Name | Description | Implementation | Location |
|--------------|-------------|----------------|----------|
| FQP1 | Guaranteed Processing | `pred fqp1` | `rollup_properties.als:73-85` |
| FQP2 | Forced Queue Stable | `pred fqp2` | `rollup_properties.als:88-99` |
| FQP3 | State Invariant | `pred fqp3` | `rollup_properties.als:102-113` |
| FQP4 | Forced Inputs Progress | `pred fqp4` | `rollup_properties.als:116-131` |
| FQP5 | Order Preservation | `pred fqp5` | `rollup_properties.als:148-164` |
| FQP6 | Finalization Confirmation | `pred fqp6` | `rollup_properties.als:135-145` |

### Blacklist Properties (BP)

| Property Name | Description | Implementation | Location |
|--------------|-------------|----------------|----------|
| BP1 | Non-blacklisted Finalization | `pred bp1` | `rollup_properties.als:167-178` |
| BP2 | Forced Queue Integrity under Censorship | `pred bp2` | `rollup_properties.als:182-191` |
| BP3 | Head Position Security | `pred bp3` | `rollup_properties.als:205-214` |
| BP4 | Future Policy Compliance | `pred bp4` | `rollup_properties.als:217-229` |
| BP5 | Following Active Policy | `pred bp5` | `rollup_properties.als:234-245` |

### Upgrade Properties (UP)

| Property Name | Description | Implementation | Location |
|--------------|-------------|----------------|----------|
| UP1 | Consistency of Upgrade Announcement, Timeout, and Enforcement | `pred up1` | `rollup_properties.als:250-268` |
| UP2 | Finalization of Forced Inputs before the Upgrade | `pred up2` | `rollup_properties.als:271-286` |
| UP3 | Post-Upgrade System Integrity | `pred up3` | `rollup_properties.als:290-299` |
| UP4 | Consistency of Blacklisting During Upgrades | `pred up4` | `rollup_properties.als:302-315` |

## Scenarios and Testing

### System Specifications (`rollup_dynamics.als:322-435`)

| Specification | Purpose | Location |
|--------------|---------|----------|
| Initial State | Empty system | `rollup_dynamics.als:322-327` |
| `spec_simple` | Basic rollup without forced queue | `rollup_dynamics.als:412-416` |
| `spec_forced_queue` | Rollup with forced queue | `rollup_dynamics.als:418-421` |
| `spec_blacklist_eager` | Eager blacklisting | `rollup_dynamics.als:423-425` |
| `spec_blacklist_soft` | Soft blacklisting with upgrades | `rollup_dynamics.als:427-430` |
| `spec_all_censored` | Full censorship scenario | `rollup_dynamics.als:432-435` |

### Property Verification

All properties are verified using Alloy's bounded model checking with commands like:
```alloy
check c_property_name {
  specification implies property
} for 5 but 1..5 steps
```

This ensures properties hold for all traces up to 5 steps with up to 5 objects of each type.

## Usage Guide

### Running Property Checks

To verify a specific property:
1. Open the Alloy Analyzer
2. Load `rollup_properties.als`
3. Execute the corresponding check command (e.g., `check c_simple_rollup_prop1`)

### Understanding Counterexamples

When a property fails:
1. The Alloy Analyzer shows a counterexample trace
2. Each state shows the values of all variables
3. The event sequence leading to the violation is displayed

### Extending the Model

To add new properties:
1. Define the property predicate in `rollup_properties.als`
2. Create a check command that tests it against appropriate specifications

## Key Implementation Details

### Sequence Operations
- Forced queue uses Alloy sequences: `rollup_data_model.als:60`
- Queue operations preserve order: `rollup_dynamics.als:151-162`

### Frame Conditions
- Every predicate includes frame conditions to specify unchanged variables
- Example: `rollup_dynamics.als:14-31` in `receive_commitment`

### Temporal Logic
- Uses Alloy's temporal operators: `always`, `eventually`, `once`, `releases`
- Example: `rollup_properties.als:20-29` uses `once` for past verification

## Model a specific Rollup implementation

To model a specific rollup you can extend/modify the provided model. In some cases some changes in the dynamics might required. For an example, look at `SCROLL.md` to understand how we modeled the forced queue mechanism of Scroll.