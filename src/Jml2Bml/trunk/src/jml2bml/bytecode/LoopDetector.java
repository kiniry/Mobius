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

public class LoopDetector {
  public static void detectLoop(final BCMethod method) {
    final MyControlFlowGraph graph = new MyControlFlowGraph(method);
    System.out.println("AAAAAA DETECT LOOP POCZATEK "
                       + method.getBcelMethod().getName());
    final InstructionContext[] instructions = graph.getInstructionContext();
    for (InstructionContext instruction : instructions) {
      firstKindLoop(instruction, graph);
      secondKindLoop(instruction, graph);
    }
    System.out.println("AAAAAA DETECT LOOP KONIEC");
  }

  private static void firstKindLoop(final InstructionContext instruction,
                                    final MyControlFlowGraph graph) {
    final List<InstructionContext> precInstr = graph
        .getPrecedingInstructions(instruction);
    final int number = graph.getInstructionNumber(instruction);
    int min = number;
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
      if (loopCondition != null) {
        System.out.println("znalazlem poczatek petli pierwszego rodzaju :"
                           + loopCondition);
      }
    }
  }

  private static void secondKindLoop(final InstructionContext instruction,
                                     final MyControlFlowGraph graph) {
    final List<InstructionContext> precInstr = graph
        .getPrecedingInstructions(instruction);
    if (precInstr.size() < 2) {
      return;
    }
    System.out.println(instruction);
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
      System.out.println(instruction + "number i max: " + number + " " + max);
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
          if (n < min) {
            min = n;
            loopStart = p;
          }
        }
      }
      if (loopStart != null) {
        System.out.println("znalazlem petle drugiego rodzaju, zaczyna sie w: "
                           + loopStart);
      }
    }
  }

}
