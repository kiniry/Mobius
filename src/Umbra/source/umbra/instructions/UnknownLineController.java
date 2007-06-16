/*
 * Created on 2005-05-17
 */
package umbra.instructions;


/**
 * This class is resposible for all lines that we cannot classify.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class UnknownLineController extends BytecodeLineController {

  /**
   * This constructor only remembers the line with the
   * unrecognized content.
   *
   * @param a_line the line with the unrecognized content
   */
  public UnknownLineController(final String a_line) {
    super(a_line);
  }

}
