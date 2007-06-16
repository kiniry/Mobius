/*
 * Created on 2005-05-19
 *
 */
package umbra.instructions;

/**
 * This is abstract class for all instructions with a string (in or
 * without <>, always without "") as a parameter.
 *
 * @author Jarosław Paszek
 *
 */
public class StringInstruction extends MultiInstruction {

  /**
   * TODO
   */
  public StringInstruction(final String l, final String n) {
    super(l, n);
  }

}
