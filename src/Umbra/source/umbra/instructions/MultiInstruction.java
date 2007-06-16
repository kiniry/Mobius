/*
 * Created on 2005-05-19
 *
 */
package umbra.instructions;

/**
 * This is abstract class for all instructions with at least one
 * parameter.
 *
 * @author Jarosław Paszek
 *
 */
public class MultiInstruction extends InstructionLineController {

  /**
   * This creates an instance of an instruction
   * named as <code>n</code> at the line number
   * <code>l</code>
   *
   * @param l the line number of the instruction
   * @param n the mnemonic name of the instruction
   */
  public MultiInstruction(final String l, final String n) {
    super(l, n);
  }

}
