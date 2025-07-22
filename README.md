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

## Running Alloy Checks through VSCode plug-in

If you install the plug-in `ArashSahebolamri.alloy` then you can run the `check` properties from `rollup_properties.als` and the `run` scenarios from `rollup_scenarios.als` through the VSCode idea by going to the definitions and click on `execute`.

## Running Alloy Checks from the Command Line (Java)

This project includes a Java utility (`AlloyRunner.java`) for running Alloy checks and saving results to CSV/XML files.

### **Requirements**
- Java 8 or later
- Alloy 6.1 libraries (must be on your classpath)
  - You can download Alloy from https://alloytools.org/download.html
  - The required JARs are typically in the `lib/` directory of the Alloy distribution (e.g., `alloy4.jar`, `alloy4compiler.jar`, `alloy4viz.jar`, `kodkod.jar`)

### Instructions to install everything in a clean Ubuntu 24.04 LTS

```

```

### **Compiling**

1. Place `AlloyRunner.java` in your project directory.
2. Download the Alloy 6.1 JARs and place them in a `lib/` directory (or anywhere you prefer).
3. Compile with:
   
   ```sh
   javac -cp "lib/*" AlloyRunner.java
   ```
   (On Windows, use `lib/*;` as the separator if needed.)

### **Running**

Run the program with:

```sh
java -cp ".:lib/*" AlloyRunner <als_file> <output_dir> [command_index]
```
- `<als_file>`: Path to your Alloy model file (e.g., `rollup_properties.als`)
- `<output_dir>`: Directory where results will be saved (must not already exist)
- `[command_index]`: (Optional) Index of the command to run (0-based). If omitted, all commands are run.

**Examples:**

- Run all commands and save results:
  ```sh
  java -cp ".:lib/*" AlloyRunner rollup_properties.als results_dir
  ```
- Run only the first command (index 0):
  ```sh
  java -cp ".:lib/*" AlloyRunner rollup_properties.als results_dir 0
  ```

**Note:**
- On Windows, replace `:` with `;` in the classpath.
- The program will create `<output_dir>` and save all CSV and XML result files there.
- If `<output_dir>` already exists, the program will exit with a message.

## Generating Custom Alloy Files with Different Scopes

This repository provides a template system for generating Alloy property files with custom scopes and step counts.
The default scope used is 5 for 5 steps which is sufficiently small to run in a timely manner in any machine. 
Yet, it is useful to run using a larger scope and steps to model check more thorough configurations and exploring deeper states for the model.

### **How it works**
- The file `rollup_properties_template_N_M.als` contains placeholders `{{N}}` and `{{M}}` in all check commands (e.g., `for {{N}} but 1..{{M}} steps`).
- The script `prepare_template.sh` takes two arguments (N and M), replaces the placeholders, and produces a file named `rollup_properties_N_M.als`.

### **Usage**

```sh
./prepare_template.sh N M
```
- Replace `N` and `M` with the desired scope and max steps (e.g., `./prepare_template.sh 10 7`)
- The script will generate a file called `rollup_properties_N_M.als` (e.g., `rollup_properties_10_7.als`)

### **Example**

To generate a file for scope 20 and 8 steps:

```sh
./prepare_template.sh 20 8
```

This will create `rollup_properties_20_8.als` with all check commands using `for 20 but 1..8 steps`.

**Note:**
- You must have `rollup_properties_template_N_M.als` in the same directory as the script.
- The script will print the output filename if successful.
