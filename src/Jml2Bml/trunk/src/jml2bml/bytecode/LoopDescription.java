/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-07 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.bytecode;

import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.verifier.structurals.InstructionContext;

/**
 * Class representing loop location in bytecode.
 * It contains 3 fields: start of the loop, end of the loop
 * and instruction to annotate (instruction to which the loop invariant
 * should be added).
 * @author Jedrek (fulara@mimuw.edu.pl)
 * @version 0-0.1
 */
public class LoopDescription {
  /** Start of the loop. */
  private InstructionContext start;

  /** End of the loop. */
  private InstructionContext end;

  /** Where to add invariant to the loop. */
  private InstructionContext add;

  /**
   * Creates the loop description object.
   * @param astart - start of the loop
   * @param anend - end of the loop
   * @param whereAdd - instruction to which the loop invariant should be added.
   */
  public LoopDescription(final InstructionContext astart,
                         final InstructionContext anend,
                         final InstructionContext whereAdd) {
    this.start = astart;
    this.end = anend;
    this.add = whereAdd;
  }

  /**
   * Returns start of the loop.
   * @return start of the loop.
   */
  public InstructionContext getLoopStart() {
    return start;
  }

  /**
   * Returns start handle of the loop.
   * @return start handle of the loop.
   */
  public InstructionHandle getLoopStartHandle() {
    return start.getInstruction();
  }

  /**
   * Returns end of the loop.
   * @return end of the loop.
   */
  public InstructionContext getLoopEnd() {
    return end;
  }

  /**
   * Returns end handle of the loop.
   * @return end handle of the loop.
   */
  public InstructionHandle getLoopEndHandle() {
    return end.getInstruction();
  }

  /**
   * Returns the instruction to annotate with the loop invariant.
   * @return instruction to annotate
   */
  public InstructionContext getInstructionToAnnotate() {
    return add;
  }

  /**
   * Returns the instruction handle to annotate with the loop invariant.
   * @return instruction handle to annotate
   */
  public InstructionHandle getInstructionHandleToAnnotate() {
    return add.getInstruction();
  }

  /**
   * Overriden toString Object method.
   * @return readable print
   */
  @Override
  public String toString() {
    return "Loop Description: (" + start.getInstruction() + "," +
           end.getInstruction() + "): " + add.getInstruction();
  }
}
