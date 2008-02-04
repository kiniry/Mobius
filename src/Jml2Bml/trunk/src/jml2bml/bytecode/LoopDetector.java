package jml2bml.bytecode;

import java.util.List;

import org.apache.bcel.verifier.structurals.InstructionContext;

import annot.bcclass.BCMethod;

/**
 * Class responsible for detecting loops in bytecode. For each loop,
 * its condition instruction is found.
 * @author Jedrek (fulara@mimuw.edu.pl)
 * @version 0-0.1
 */
public final class LoopDetector {

  /**
   * Hidden constructor.
   */
  private LoopDetector() {

  }

  /**
   * Detects all loops in the given method.
   * @param method - given method
   */
  public static void detectLoop(final BCMethod method) {
    final MyControlFlowGraph graph = new MyControlFlowGraph(method);
    final InstructionContext[] instructions = graph.getInstructionContext();
    for (InstructionContext instruction : instructions) {
      InstructionContext loopCondition = null;
      loopCondition = firstKindLoop(instruction, graph);
      if (loopCondition != null) {
        System.out.println("for method " + method.getBcelMethod().getName()
                           + " found first loop type! Condition is at "
                           + loopCondition);
      } else {
        loopCondition = secondKindLoop(instruction, graph);
        if (loopCondition != null) {
          System.out.println("for method " + method.getBcelMethod().getName()
                             + " found second loop type! Condition is at "
                             + loopCondition);
        }
      }
    }
  }

  /**
   * Determines whether the given instruction is the beginning
   * of loading loop condition parameters.
   * If yes, finds the loop condition statement
   * (the instruction to which we want to assign the loop invariants)
   * This method recognizes following type of loops:
   * <code><br>
   * [1] ...<br>
   * [2] goto [4]<br>
   * [3] loop body<br>
   * [4] load condition parameters<br>
   * [5] if condition is satisfied jump to [3]<br>
   * [6] ...<br>
   * </code><br>
   * @param instruction tested instruction
   * @param graph control flow graph for a method
   * @return the loop condition statement or null
   */
  private static InstructionContext firstKindLoop(
                                                  final InstructionContext instruction,
                                                  final MyControlFlowGraph graph) {
    final List<InstructionContext> precInstr = graph
        .getPrecedingInstructions(instruction);
    final int number = graph.getInstructionNumber(instruction);
    int min = number - 1;
    InstructionContext beforeLoop = null;
    for (InstructionContext prec : precInstr) {
      final int n = graph.getInstructionNumber(prec);
      if (n < min) {
        min = n;
        beforeLoop = prec;
      }
    }
    if (beforeLoop != null) {
      InstructionContext loopCondition = null;
      final InstructionContext c = graph.getNextInstruction(beforeLoop);
      final List<InstructionContext> prec = graph.getPrecedingInstructions(c);
      int max = number;
      for (InstructionContext p : prec) {
        final int n = graph.getInstructionNumber(p);
        if (n > max) {
          max = n;
          loopCondition = p;
        }
      }
      return loopCondition;
    }
    return null;
  }

  /**
   * Determines, whether given instruction is a very beginning of a loop
   * (start of loading condition parameters). If yes - returns the condition
   * instruction (after all condition parameters are loaded). This method
   * handles following type of loops:
   * <code><br>
   * [1] ... <br>
   * [2] load condition parameters<br>
   * [3] if condition is false, jump to [6]<br>
   * [4] loop body<br>
   * [5] goto [2]<br>
   * [6] ...<br>
   * </code><br>
   * @param instruction instruction to check
   * @param graph control flow graph for a method
   * @return the loop condition instruction
   */
  private static InstructionContext secondKindLoop(
                                                   final InstructionContext instruction,
                                                   final MyControlFlowGraph graph) {
    final List<InstructionContext> precInstr = graph
        .getPrecedingInstructions(instruction);
    if (precInstr.size() < 2){
      return null;
    }
    final int number = graph.getInstructionNumber(instruction);
    int max = number;
    InstructionContext loopEnd = null;
    for (InstructionContext prec : precInstr) {
      final int n = graph.getInstructionNumber(prec);
      if (n > max) {
        max = n;
        loopEnd = prec;
      }
    }
    if (loopEnd != null) {
      //now max is the number of the line with the longest jump;
      InstructionContext loopStart = null;
      final InstructionContext c = graph.getNextInstruction(loopEnd);
      if (c == null) {
        //special case, loop condition is "true"
        loopStart = instruction;
      } else {
        final List<InstructionContext> prec = graph.getPrecedingInstructions(c);
        int min = max + 1;
        for (InstructionContext p : prec) {
          final int n = graph.getInstructionNumber(p);
          if (n < min && n >= number) {
            min = n;
            loopStart = p;
          }
        }
      }
      return loopStart;
    }
    return null;
  }

}
