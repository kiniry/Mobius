package umbra.instructions;


/**
 * This is a class for a line with whitespaces only.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class EmptyLineController extends BytecodeLineController {

  /**
   * This constructor remembers only the line text of the line which contains
   * solely whitespaces.
   *
   * @param a_line_text the string representation of the line
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public EmptyLineController(final String a_line_text) {
    super(a_line_text);
  }

  /**
   * @return  true - an empty line is always correct
   * @see BytecodeLineController#correct()
   */
  public final boolean correct()
  {
    //sprawdzanie poprawnosci juz przy wyborze typu
    return true;
  }
}
