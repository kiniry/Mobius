/*
 * Created on 2005-05-19
 *
 */
package umbra.instructions;

/**
 * This is abstract class for all instructions with at least one
 * parameter.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class MultiInstruction extends InstructionLineController {

  /**
   * This creates an instance of an instruction
   * named as <code>a_name</code> at the line number
   * <code>a_line</code>.
   *
   * @param a_line the line number of the instruction
   * @param a_name the mnemonic name of the instruction
   */
  public MultiInstruction(final String a_line, final String a_name) {
    super(a_line, a_name);
  }

}
