/*
 * Created on 2005-05-18
 *
 */
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
   * TODO
   */
  public ThrowsLineController(final String l) {
    super(l);
  }


  /**
   * TODO
   */
  public final boolean correct()
  {
    //tez niezbyt - patrz przy wyborze typu - nie za bardzo wiemy jak wyglada
    return true;
  }
}
