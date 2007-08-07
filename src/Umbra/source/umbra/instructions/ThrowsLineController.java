package umbra.instructions;


/**
 * This is a class for a special Bytecode lines related to
 * thrown exceptions, not to be edited by a user.
 *
 * @author Tomek Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class ThrowsLineController extends BytecodeLineController {

  /**
   * This constructor remembers only the line text of a line with the throws
   * instruction.
   *
   * @param a_line_text the string representation of the line
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public ThrowsLineController(final String a_line_text) {
    super(a_line_text);
  }


  /**
   * TODO we don't quite know how it looks like as the type is given.
   * @return currently, it returns always <code>true</code>
   */
  public final boolean correct() {
    return true;
  }
}
