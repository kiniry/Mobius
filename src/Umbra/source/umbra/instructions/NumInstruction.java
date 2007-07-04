/*
 * Created on 2005-05-19
 *
 */
package umbra.instructions;

/**
 * This is abstract class for all instructions with a number as a
 * parameter.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class NumInstruction extends MultiInstruction {


  /**
   * This creates an instance of an instruction
   * named as <code>a_name</code> in a line the text of which is
   * <code>a_line_text</code>. Currently it just calls the constructor of the
   * superclass.
   *
   * @param a_line_text the line number of the instruction
   * @param a_name the mnemonic name of the instruction
   * @see InstructionLineController#InstructionLineController(String, String)
   */
  public NumInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }
}
