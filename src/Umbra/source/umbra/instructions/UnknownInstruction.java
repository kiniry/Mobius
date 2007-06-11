/*
 * Created on 2005-05-19
 *
 */
package umbra.instructions;


/**
 * This is a class resposible for all lines which are regarded
 * to be an instruction but unable to classify.
 *
 * @author Tomek Batkiewicz i Jarosław Paszek
 */
public class UnknownInstruction extends InstructionLineController {


  /**
   * This constructor remembers only the content of the line
   * and the form of the mnemonic.
   *
   * @param l the line with the unknown mnemonic
   * @param n the unknown mnemonic
   */
  public UnknownInstruction(String l, String n) {
    super(l, n);
  }
  /**
   * Instruction out of classification must be obviously incorrect.
   *
   * @see  InstructionLineController#correct()
   */
  public boolean correct() {
    return false;
  }
}
