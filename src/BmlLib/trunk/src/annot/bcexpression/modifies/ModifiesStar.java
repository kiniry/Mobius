package annot.bcexpression.modifies;

import annot.io.Code;
import annot.textio.BMLConfig;

/**
 * This class describes modification of all elements
 * of an array.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class ModifiesStar extends SpecArray {

  public ModifiesStar() {
    super(Code.MODIFIES_STAR);
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return "*";
  }

  @Override
  public String toString() {
    return "[*]";
  }

}
