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

/**
 * Control flow graph, providing access to preceding instructions,
 * successors, instruction numbers etc.
 * @author Jedrek (fulara@mimuw.edu.pl)
 * @version 0-0.1
 */
public class MyControlFlowGraph {

  /**
   * Array of all instructions in the method.
   */
  private InstructionContext[] contexts;

  /**
   * Map storing lists of preceding instructions.
   */
  private Map<InstructionContext, List<InstructionContext>> prec;

  /**
   * Map storing instruction numbers.
   */
  private Map<InstructionContext, Integer> instrNum;

  /**
   * Map storing next instruction for the given one.
   */
  private Map<InstructionContext, InstructionContext> nextInstruction;

  /**
   * Constructs the extended control flow graph for given method.
   * @param method method, for which the control flow graph should be
   * constructed.
   */
  public MyControlFlowGraph(final BCMethod method) {
    final MethodGen mgen = method.getBcelMethod();
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
    final Map<InstructionContext, Integer> res =
      new HashMap<InstructionContext, Integer>();
    final InstructionHandle[] instr = mgen.getInstructionList()
        .getInstructionHandles();
    final Map<InstructionHandle, Integer> tmp =
      new HashMap<InstructionHandle, Integer>();
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
    final Map<InstructionContext, InstructionContext> res =
      new HashMap<InstructionContext, InstructionContext>();
    final InstructionHandle[] instr = mgen.getInstructionList()
        .getInstructionHandles();
    final Map<InstructionHandle, InstructionContext> tmp =
      new HashMap<InstructionHandle, InstructionContext>();
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
  private Map<InstructionContext,
              List<InstructionContext>> getIncomingInstructions() {
    final Map<InstructionContext, List<InstructionContext>> res =
      new HashMap<InstructionContext, List<InstructionContext>>();
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

  /**
   * Returns array of all instructions in the method. They don't have to be
   * ordered!
   * @return array of all instructions in the method.
   */
  public InstructionContext[] getInstructionContext() {
    return contexts;
  }

  /**
   * Returns the list of preceding instructions for given instruction.
   * <code>a</code> is a preceding instruction for <code>b</code>,
   * if there is an edge <code>a->b</code> in the control flow graph
   * @param instruction instruction, for which preceding instructions
   * should be found
   * @return list of preceding instructions
   */
  public List<InstructionContext> getPrecedingInstructions(
      final InstructionContext instruction) {
    return prec.get(instruction);
  }

  /**
   * Returns the number of given instruction in the method.
   * @param instruction instruction for which the number should be found.
   * @return the number of given instruction in the method
   */
  public int getInstructionNumber(final InstructionContext instruction) {
    return instrNum.get(instruction);
  }

  /**
   * Returns the next instruction (not a successor in the control flow graph,
   * but simply the next instruction in the method).
   * @param instruction instruction, for which the next instruction should be
   * found
   * @return next instruction
   */
  public InstructionContext getNextInstruction(
      final InstructionContext instruction) {
    return nextInstruction.get(instruction);
  }
}
