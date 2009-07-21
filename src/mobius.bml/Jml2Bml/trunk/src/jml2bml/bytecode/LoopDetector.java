package jml2bml.bytecode;

import java.util.LinkedList;
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
   * @return list of loop descriptions (condition, start, end)
   */
  public static List < LoopDescription > detectLoop(final BCMethod method) {
    if (method.getInstructions() == null){
      //abstract method
      return new LinkedList<LoopDescription>();
    }
    final MyControlFlowGraph graph = new MyControlFlowGraph(method);
    final InstructionContext[] instructions = graph.getInstructionContext();
    final List < LoopDescription > res = new LinkedList < LoopDescription >();
    for (InstructionContext instruction : instructions) {
      LoopDescription loopDescription = null;
      loopDescription = firstKindLoop(instruction, graph);
      if (loopDescription != null) {
        System.out.println("znalazlem petle pierwszego rodzaju: " +
                           loopDescription.getInstructionToAnnotate() +
                           " poczatek " + loopDescription.getLoopStart());
        res.add(loopDescription);
      } else {
        loopDescription = secondKindLoop(instruction, graph);
        if (loopDescription != null) {
          res.add(loopDescription);
        } else {
          loopDescription = findDoWhileLoop(instruction, graph);
          if (loopDescription != null) {
            res.add(loopDescription);
          }

        }
      }
    }
    return res;
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
   * @return triple (start [3], end [5], condition [5])
   */
  private static LoopDescription firstKindLoop(
      final InstructionContext instruction,
      final MyControlFlowGraph graph) {
    final List < InstructionContext > precInstr = graph
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
    InstructionContext start = null;
    if (beforeLoop != null) {
      InstructionContext loopCondition = null;
      start = findFirstLoopStart(beforeLoop, number, graph);
      if (start == null) {
        return null;
      }
      final List < InstructionContext > prec = graph
          .getPrecedingInstructions(start);
      int max = number;
      for (InstructionContext p : prec) {
        final int n = graph.getInstructionNumber(p);
        if (n > max) {
          max = n;
          loopCondition = p;
        }
      }
      if (loopCondition == null)
        return null;
      return new LoopDescription(start, loopCondition, loopCondition);
    }
    return null;
  }

  private static InstructionContext findFirstLoopStart(
      final InstructionContext beforeLoop,
      final int number,
      final MyControlFlowGraph graph) {
    InstructionContext tmp = beforeLoop;
    int n = graph.getInstructionNumber(tmp);

    while (n < number) {
      tmp = graph.getNextInstruction(tmp);
      n = graph.getInstructionNumber(tmp);
      final List < InstructionContext > prec = graph
          .getPrecedingInstructions(tmp);
      for (InstructionContext p : prec) {
        if (graph.getInstructionNumber(p) > number) {
          return tmp;
        }
      }
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
   * @return triple (start [2], end [5], loopCondition [3])
   */
  private static LoopDescription secondKindLoop(
      final InstructionContext instruction,
      final MyControlFlowGraph graph) {
    final List < InstructionContext > precInstr = graph
        .getPrecedingInstructions(instruction);
    if (precInstr.size() <= 1) {
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
      if (c != null) {
        final List < InstructionContext > prec = graph
            .getPrecedingInstructions(c);
        int min = max;
        for (InstructionContext p : prec) {
          final int n = graph.getInstructionNumber(p);
          if (n < min && n >= number) {
            min = n;
            loopStart = p;
          }
        }
      }
      if (loopStart == null) {
        return null;
      }
      if (!isConditional(loopStart)) {
        loopStart = instruction;
      }
      return new LoopDescription(instruction, loopEnd, loopStart);
    }
    return null;
  }

  /**
   * Tries to detect following kind of loop:
   * <code>[0] ...<br>
   * [1] loop body<br>
   * [2] load parameters<br>
   * [3] if condition is fulfilled goto 1<br>
   * [4] ...<br>
   * </code>
   * This function is invoked only, when no other loop type was detected.
   * @param instruction - candidate for <code>[3]</code>
   * @param graph control flow graph for the method
   * @return ([1],[3],[1])
   */
  private static LoopDescription findDoWhileLoop(
      final InstructionContext instruction,
      final MyControlFlowGraph graph) {
    final int number = graph.getInstructionNumber(instruction);
    for (InstructionContext next : instruction.getSuccessors()) {
      final int n = graph.getInstructionNumber(next);
      if (n < number) {
        for (InstructionContext instr : graph.getPrecedingInstructions(next)) {
          if (graph.getInstructionNumber(instr) < n || n == 0) {
            //the instruction just before the "next" is not a goto
            return new LoopDescription(next, instruction, next);
          }
        }
      }
    }
    return null;
  }

  /**
   * Checks if given instruction is conditional (has more than one successor).
   * @param instruction instruction to check
   * @return if the given instruction is conditional
   */
  private static boolean isConditional(final InstructionContext instruction) {
    return instruction.getSuccessors().length > 1;
  }

}
