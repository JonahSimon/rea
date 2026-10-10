import ghidra.app.cmd.disassemble.DisassembleCommand;
import ghidra.app.cmd.function.CreateFunctionCmd;
import ghidra.app.plugin.core.analysis.AutoAnalysisManager;
import ghidra.app.script.GhidraScript;
import ghidra.app.services.Analyzer;
import ghidra.app.util.PseudoDisassembler;
import ghidra.app.util.importer.MessageLog;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressSet;
import ghidra.program.model.listing.*;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.pcode.Varnode;
import ghidra.program.model.symbol.FlowType;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

/**
 * Undo wrong no-return flags from auto-analysis. A function flagged no-return that contains a
 * real RET is an ordinary function (stream readers, cxa_guard_acquire, ...). Callers treated the
 * call as a terminator and the decompiler truncated them. Clear the flag, then re-disassemble only
 * the call sites of the functions that were cleared, refit their owning functions in place and
 * restore the references of the re-disassembled code with a scoped analyzer pass.
 *
 * <p>Known limitation: when the wrongly flagged function is a PLT stub or an external with no body
 * (glibc error()), there is no RET to find, so nothing is cleared.
 */
public final class ReaGhidraNoReturnFix extends GhidraScript {
  @Override
  public void run() throws Exception {
    // Windows P0 does not admit analysis-database mutation.
    if (System.getProperty("os.name", "").startsWith("Windows")) return;
    FunctionManager fm = currentProgram.getFunctionManager();
    Listing li = currentProgram.getListing();
    Set<Address> cleared = new HashSet<>();
    for (Function f : fm.getFunctions(true)) {
      monitor.checkCancelled();
      if (!f.hasNoReturn() || f.isThunk()) continue;
      for (Instruction ins : li.getInstructions(f.getBody(), true)) {
        FlowType ft = ins.getFlowType();
        boolean decodedReturn = false;
        for (PcodeOp operation : ins.getPcode()) {
          if (operation.getOpcode() == PcodeOp.RETURN) decodedReturn = true;
        }
        if (decodedReturn && !ft.isJump() && !ft.isCall()) {
          f.setNoReturn(false);
          cleared.add(f.getEntryPoint());
          break;
        }
      }
    }
    // A thunk inherits the flag of the function it forwards to.
    for (Function f : fm.getFunctions(true)) {
      monitor.checkCancelled();
      if (!f.isThunk()) continue;
      Function target = f.getThunkedFunction(true);
      if (target != null && cleared.contains(target.getEntryPoint())) {
        cleared.add(f.getEntryPoint());
      }
    }
    int redone = 0;
    AddressSet restored = new AddressSet();
    TreeSet<Address> owners = new TreeSet<>();
    if (!cleared.isEmpty()) {
      List<Address> sites = new ArrayList<>();
      for (Instruction ins : li.getInstructions(true)) {
        monitor.checkCancelled();
        FlowType ft = ins.getFlowType();
        if (!(ft.isCall() && ft.isTerminal())) continue;
        Address[] flows = ins.getFlows();
        if (flows.length == 0 || !cleared.contains(flows[0])) continue;
        if (endsFunction(ins)) continue;
        sites.add(ins.getAddress());
      }
      for (Address s : sites) {
        monitor.checkCancelled();
        Instruction ins = li.getInstructionAt(s);
        if (ins == null) continue;
        Function owner = fm.getFunctionContaining(s);
        if (owner != null && !owner.isThunk()) owners.add(owner.getEntryPoint());
        clearListing(ins.getMinAddress(), ins.getMaxAddress());
        DisassembleCommand dc = new DisassembleCommand(s, null, true);
        dc.enableCodeAnalysis(false);
        dc.applyTo(currentProgram, monitor);
        restored.add(dc.getDisassembledAddressSet());
        redone++;
      }
      for (Address e : owners) {
        monitor.checkCancelled();
        Function f = fm.getFunctionAt(e);
        // Refit the body in place so the name, signature and calling convention survive.
        if (f != null) CreateFunctionCmd.fixupFunctionBody(currentProgram, f, monitor);
      }
      restoreReferences(restored);
    }
    println(
        "REA no-return fix: cleared=" + cleared.size() + " sites=" + redone + " refit=" + owners.size());
  }

  /**
   * Run only the reference analyzers over the restored code. analyzeChanges would re-run the
   * no-return analyzer and flag every cleared function again.
   */
  private void restoreReferences(AddressSet restored) throws Exception {
    if (restored.isEmpty()) return;
    long t0 = System.currentTimeMillis();
    AutoAnalysisManager mgr = AutoAnalysisManager.getAnalysisManager(currentProgram);
    MessageLog log = new MessageLog();
    String constants = currentProgram.getLanguage().getProcessor() + " Constant Reference Analyzer";
    for (String name : new String[] {"Reference", constants}) {
      Analyzer a = mgr.getAnalyzer(name);
      if (a == null) continue;
      a.optionsChanged(
          currentProgram.getOptions(Program.ANALYSIS_PROPERTIES).getOptions(a.getName()),
          currentProgram);
      long t1 = System.currentTimeMillis();
      a.added(currentProgram, restored, monitor, log);
      println("REA no-return fix: " + name + " " + (System.currentTimeMillis() - t1) + " ms");
    }
    println(
        "REA no-return fix: restored "
            + restored.getNumAddresses()
            + " addresses in "
            + (System.currentTimeMillis() - t0)
            + " ms");
  }

  /**
   * True when the call is the last instruction of its function: after stepping over NOPs (as
   * FindNoReturnFunctionsAnalyzer.skipNOPS does) the next thing is a function entry, defined data
   * or memory that is unmapped or does not decode. Anything else is code the flag cut off. The cut
   * off bytes are still undefined, so they are decoded with a pseudo disassembler, not the listing.
   */
  private boolean endsFunction(Instruction call) {
    FunctionManager fm = currentProgram.getFunctionManager();
    Listing li = currentProgram.getListing();
    PseudoDisassembler pd = new PseudoDisassembler(currentProgram);
    Address a = call.getMaxAddress().next();
    for (int count = 0; count < 32; count++) {
      if (a == null || !currentProgram.getMemory().contains(a)) return true;
      if (fm.getFunctionAt(a) != null || li.getDefinedDataAt(a) != null) return true;
      Instruction ins = li.getInstructionAt(a);
      try {
        if (ins == null) ins = pd.disassemble(a);
      } catch (Exception e) {
        return true;
      }
      // int3 filler is skipped like a NOP, but only counts as padding if a function entry follows.
      boolean filler = ins.getMnemonicString().equalsIgnoreCase("INT3");
      if (!filler && (!ins.getFlowType().isFallthrough() || !isNop(ins))) return false;
      a = ins.getMaxAddress().next();
    }
    return false;
  }

  /** Same test as skipNOPS: no load, store, callother or write to a non-temporary varnode. */
  private boolean isNop(Instruction ins) {
    for (PcodeOp op : ins.getPcode()) {
      switch (op.getOpcode()) {
        case PcodeOp.LOAD, PcodeOp.STORE, PcodeOp.CALLOTHER, PcodeOp.SEGMENTOP -> {
          return false;
        }
        default -> {}
      }
      Varnode out = op.getOutput();
      if (out != null && !out.isUnique()) return false;
    }
    return true;
  }
}
