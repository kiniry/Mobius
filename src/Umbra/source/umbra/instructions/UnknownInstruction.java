/*
 * Created on 2005-05-19
 *
 */
package umbra.instructions;


/**
 * This is a class resposible for all lines which are regarded
 * to be an instruction but unable to classify.
 *
 * @author Tomek Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class UnknownInstruction extends InstructionLineController {


  /**
   * This constructor remembers only the content of the line
   * and the form of the mnemonic.
   *
   * @param l the line with the unknown mnemonic
   * @param n the unknown mnemonic
   */
  public UnknownInstruction(final String l, final String n) {
    super(l, n);
  }
  /**
   * Instruction out of classification must be obviously incorrect.
   *
   * @see  InstructionLineController#correct()
   */
  public final boolean correct() {
    return false;
  }
}
