package jml2bml.bytecode;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.verifier.structurals.ControlFlowGraph;
import org.apache.bcel.verifier.structurals.InstructionContext;

import annot.bcclass.BCMethod;

public class MyControlFlowGraph {

  private InstructionContext[] contexts;

  private Map<InstructionContext, List<InstructionContext>> prec;

  private Map<InstructionContext, Integer> instrNum;

  private Map<InstructionContext, InstructionContext> nextInstruction;

  public MyControlFlowGraph(BCMethod method) {
    final MethodGen mgen = method.getBcelMethod();
    System.out.println("AAAAAA DETECT LOOP POCZATEK" + mgen.getName());
    final ControlFlowGraph graph = new ControlFlowGraph(mgen);
    contexts = graph.getInstructionContexts();
    prec = getIncomingInstructions();
    instrNum = getInstrNum(mgen);
    nextInstruction = getNextInstructionMap(mgen);
  }

  /**
   * Associates the instruction context with the instruction number
   * in given method.
   * @param mgen given method
   * @return map Instruction Context -> its number
   */
  private Map<InstructionContext, Integer> getInstrNum(final MethodGen mgen) {
    final Map<InstructionContext, Integer> res = new HashMap<InstructionContext, Integer>();
    final InstructionHandle[] instr = mgen.getInstructionList()
        .getInstructionHandles();
    final Map<InstructionHandle, Integer> tmp = new HashMap<InstructionHandle, Integer>();
    for (int i = 0; i < instr.length; i++) {
      tmp.put(instr[i], i);
    }
    for (InstructionContext context : contexts) {
      res.put(context, tmp.get(context.getInstruction()));
    }
    return res;
  }

  /**
   * Finds next instruction (not the successor!) for each instruction
   * in the given method.
   * @param mgen method to analyse
   * @return map instruction -> next instruction.
   */
  private Map<InstructionContext, InstructionContext> getNextInstructionMap(
                                                                            final MethodGen mgen) {
    final Map<InstructionContext, InstructionContext> res = new HashMap<InstructionContext, InstructionContext>();
    final InstructionHandle[] instr = mgen.getInstructionList()
        .getInstructionHandles();
    final Map<InstructionHandle, InstructionContext> tmp = new HashMap<InstructionHandle, InstructionContext>();
    for (InstructionContext context : contexts) {
      tmp.put(context.getInstruction(), context);
    }
    for (int i = 0; i < instr.length; i++) {
      InstructionContext value = null;
      if (i < instr.length - 1) {
        value = tmp.get(instr[i + 1]);
      }
      res.put(tmp.get(instr[i]), value);
    }
    return res;
  }

  /**
   * Finds the list of instructions preceding the given one in the
   * flow control graph.
   * @return instruction -> list of preceding instructions.
   */
  private Map<InstructionContext, List<InstructionContext>> getIncomingInstructions() {
    final Map<InstructionContext, List<InstructionContext>> res = new HashMap<InstructionContext, List<InstructionContext>>();
    for (InstructionContext context : contexts) {
      res.put(context, new LinkedList<InstructionContext>());
    }
    for (InstructionContext context : contexts) {
      for (InstructionContext succ : context.getSuccessors()) {
        final List<InstructionContext> list = res.get(succ);
        list.add(context);
        res.put(succ, list);
      }
    }
    return res;
  }

  public InstructionContext[] getInstructionContext() {
    return contexts;
  }

  public List<InstructionContext> getPrecedingInstructions(final InstructionContext instruction){
    return prec.get(instruction);
  }
  
  public int getInstructionNumber(final InstructionContext instruction){
    return instrNum.get(instruction);
  }
  
  public InstructionContext getNextInstruction(final InstructionContext instruction){
    return nextInstruction.get(instruction);
  }
}
