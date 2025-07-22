import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.CommandScope;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;
import kodkod.engine.satlab.SATFactory;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class AlloyRunner {
    
    public static final int SOLVER_TIMEOUT_SECONDS = 1;
    
    static class AlloyReporter extends A4Reporter {
        private long startTime;
        private int currentStep = 1;
        private boolean firstStep = true;
        private Command command;
        private int minSteps = 1;
        private int maxSteps = 5;
        private int actualMaxSteps = 5;
        private String commandStr;
        private String scope;
        private String finalStatus = "UNKNOWN";
        private List<String[]> csvData = new ArrayList<>();
        
        public void setCommand(Command cmd) {
            this.command = cmd;
            // Extract steps from command if available
            if (cmd.expects > 0) {
                this.minSteps = cmd.expects;
                this.maxSteps = cmd.expects;
            }
            
            // Look for steps in command scopes
            for (int i = 0; i < cmd.scope.size(); i++) {
                CommandScope cs = cmd.scope.get(i);
                if (cs.sig != null && cs.sig.label.equals("steps")) {
                    this.minSteps = cs.startingScope;
                    this.maxSteps = cs.endingScope;
                }
            }
        }
        
        @Override
        public void translate(String solver, int bitwidth, int maxseq, int skolemDepth, int symmetry, int intEncoding, int arrayEncoding, String originalFilename) {
            System.out.println("Starting the solver...");
            System.out.println();
            
            // Build the execution string using command.toString() which has the full command text
            commandStr = command.toString();
            System.out.println(String.format("Executing \"%s\"", commandStr));
            
            // Extract scope
            scope = String.valueOf(command.overall);
            
            // Get solver name properly
            String solverName = solver.toLowerCase();
            if (solverName.contains("sat4j")) {
                solverName = "sat4j";
            }
            
            // Extract steps from command string if present
            String stepsDisplay = null;
            if (commandStr.contains(" but ")) {
                String afterBut = commandStr.substring(commandStr.indexOf(" but ") + 5);
                if (afterBut.contains(" steps")) {
                    stepsDisplay = afterBut.substring(0, afterBut.indexOf(" steps")).trim();
                }
            }
            
            // If no steps specified, Alloy uses default 1..10
            if (stepsDisplay == null) {
                stepsDisplay = "1..10";
            }
            
            System.out.println(String.format("Solver=%s Steps=%s Bitwidth=%d MaxSeq=%d SkolemDepth=%d Symmetry=%d Mode=batch",
                solverName, stepsDisplay, bitwidth, maxseq, skolemDepth, symmetry));
            System.out.println("Generating CNF...");
            startTime = System.currentTimeMillis();
        }
        
        @Override
        public void solve(int p0, int p1, int p2, int p3) {
            long elapsed = System.currentTimeMillis() - startTime;
            
            // Based on comparing with original output:
            // Original shows: "6672 vars. 155 primary vars. 14477 clauses"
            // p1 matches the primary vars from original (155, 310, 465...)
            // p2 might be total vars, p3 might be clauses
            int primaryVars = p1;
            int vars = p2;
            int clauses = p3;
            
            // Track actual max steps being solved
            actualMaxSteps = Math.max(actualMaxSteps, currentStep);
            
            String stepRange;
            if (currentStep == 1) {
                stepRange = "1..1";
            } else {
                stepRange = "1.." + currentStep;
            }
            
            if (firstStep) {
                System.out.println(String.format("%s steps. %d vars. %d primary vars. %d clauses. %dms.",
                    stepRange, vars, primaryVars, clauses, elapsed));
                firstStep = false;
            } else {
                System.out.println("Solving...");
                System.out.println(String.format("%s steps. %d vars. %d primary vars. %d clauses. %dms.",
                    stepRange, vars, primaryVars, clauses, elapsed));
            }
            
            // Save to CSV data
            String[] row = {
                commandStr,
                scope,
                stepRange,
                String.valueOf(vars),
                String.valueOf(primaryVars),
                String.valueOf(clauses),
                elapsed + "ms",
                "PENDING"  // Status will be updated later
            };
            csvData.add(row);
            
            currentStep++;
        }
        
        @Override
        public void resultSAT(Object command, long solvingTime, Object solution) {
            System.out.println(String.format("Counterexample found. %dms.", solvingTime));
            finalStatus = "SAT";
            
            // Only mark the last row (the successful step) as SAT
            if (!csvData.isEmpty()) {
                String[] lastRow = csvData.get(csvData.size() - 1);
                lastRow[7] = "SAT";
            }
            
            // Mark all previous rows as UNSAT (they didn't find counterexamples)
            for (int i = 0; i < csvData.size() - 1; i++) {
                csvData.get(i)[7] = "UNSAT";
            }
        }
        
        @Override
        public void resultUNSAT(Object command, long solvingTime, Object solution) {
            System.out.println(String.format("No counterexample found. Assertion may be valid. %dms.", solvingTime));
            finalStatus = "UNSAT";
            
            // Mark all rows as UNSAT
            for (String[] row : csvData) {
                row[7] = "UNSAT";
            }
        }
        
        public void writeCsvFile(String filename) throws IOException {
            try (FileWriter writer = new FileWriter(filename)) {
                // Write header
                writer.write("Command,Scope,Step,Vars,Primary Vars,Clauses,Time,Status\n");
                
                // Write data
                for (String[] row : csvData) {
                    writer.write(String.join(",", row) + "\n");
                }
            }
            System.out.println("CSV file written to: " + filename);
        }
    }
    
    public static void main(String[] args) throws Err {
        if (args.length < 2) {
            System.err.println("Usage: java AlloyVSCodeRunner <als_file> <output_dir> [command_index]");
            System.err.println("  <als_file>: Alloy model file");
            System.err.println("  <output_dir>: Directory to save results (must not exist)");
            System.err.println("  [command_index]: Optional, if provided only that command will be executed");
            System.exit(1);
        }
        
        String filename = args[0];
        String outputDir = args[1];
        Integer commandIndex = null;
        
        File dir = new File(outputDir);
        if (dir.exists()) {
            System.out.println("Directory already exists: " + outputDir);
            System.exit(1);
        } else {
            if (dir.mkdirs()) {
                System.out.println("Results will be saved in directory: " + outputDir);
            } else {
                System.err.println("Failed to create directory: " + outputDir);
                System.exit(1);
            }
        }
        
        if (args.length > 2) {
            try {
                commandIndex = Integer.parseInt(args[2]);
            } catch (NumberFormatException e) {
                System.err.println("[command_index] must be an integer if provided");
                System.exit(1);
            }
        }
        
        A4Reporter tempRep = new A4Reporter();
        Module world = CompUtil.parseEverything_fromFile(tempRep, null, filename);
        
        A4Options options = new A4Options();
        options.solver = SATFactory.DEFAULT;
        options.skolemDepth = 1;
        options.symmetry = 20;
        
        if (commandIndex != null) {
            if (commandIndex >= world.getAllCommands().size()) {
                System.err.println("Command index out of range");
                System.exit(1);
            }
            runCommand(world, options, commandIndex, outputDir);
        } else {
            System.out.println("Found " + world.getAllCommands().size() + " commands. Running all...");
            System.out.println();
            for (int i = 0; i < world.getAllCommands().size(); i++) {
                System.out.println("=== Running Command " + i + " ===");
                runCommand(world, options, i, outputDir);
                System.out.println();
            }
            System.out.println("All commands completed.");
        }
    }
    
    private static void runCommand(Module world, A4Options options, int commandIndex, String outputDir) throws Err {
        AlloyReporter rep = new AlloyReporter();
        Command cmd = world.getAllCommands().get(commandIndex);
        rep.setCommand(cmd);
        A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), cmd, options);
        if (ans.satisfiable()) {
            String xmlFilename = outputDir + File.separator + "counterexample_cmd" + commandIndex + ".xml";
            try {
                ans.writeXML(xmlFilename);
                System.out.println("Counterexample saved to: " + xmlFilename);
            } catch (Exception e) {
                System.err.println("Warning: Could not write counterexample XML file: " + e.getMessage());
                System.out.println("Counterexample found but could not be saved to XML.");
            }
        }
        // Write CSV file
        try {
            String csvFilename = outputDir + File.separator + "alloy_results_cmd" + commandIndex + ".csv";
            rep.writeCsvFile(csvFilename);
        } catch (IOException e) {
            System.err.println("Error writing CSV file: " + e.getMessage());
        }
    }
}