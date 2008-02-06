package jml2bml.bytecode;

import org.apache.bcel.verifier.structurals.InstructionContext;

/**
 * Class representing loop location in bytecode.
 * It contains 3 fields: start of the loop, end of the loop
 * and instruction to annotate (instruction to which the loop invariant
 * should be added).
 * @author Jedrek
 */
public class LoopDescription {
  private InstructionContext start;

  private InstructionContext end;

  private InstructionContext add;

  /**
   * Creates the loop description object
   * @param start - start of the loop
   * @param end - end of the loop
   * @param whereAdd - instruction to which the loop invariant should be added.
   */
  public LoopDescription(final InstructionContext start,
                         final InstructionContext end,
                         final InstructionContext whereAdd) {
    this.start = start;
    this.end = end;
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
   * Returns end of the loop.
   * @return end of the loop.
   */
  public InstructionContext getLoopEnd() {
    return end;
  }

  /**
   * Returns the instruction to annotate with the loop invariant.
   * @return instruction to annotate
   */
  public InstructionContext getInstructionToAnnotate() {
    return add;
  }
}
