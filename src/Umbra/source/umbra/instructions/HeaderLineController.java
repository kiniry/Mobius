/*
 * Created on 2005-05-18
 *
 */
package umbra.instructions;


/**
 * This is a class for a special Bytecode lines at the beginning
 * of the method, not to be edited by a user.
 *
 * @author Tomek Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class HeaderLineController extends BytecodeLineController {

  /**
   * TODO
   */
  public HeaderLineController(final String l) {
    super(l);
  }

  /**
   * TODO
   */
  public final boolean correct()
  {
    //niz za bardzo mozna ustalic zaleznosci
    //zbior wyrazow przed innym niektore opcjonalne
    return true;
  }

  /**
   * The method index of the header is equal to
   * the previous line's one increased by one.
   * TODO
   */
  public final void setIndex(final int index2) {
    this.index = index2 + 1;
  }
}
