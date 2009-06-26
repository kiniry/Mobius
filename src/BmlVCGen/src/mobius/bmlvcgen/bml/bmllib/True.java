package mobius.bmlvcgen.bml.bmllib;

import mobius.bmlvcgen.bml.ExprVisitor;
import mobius.bmlvcgen.util.Visitable;

/**
 * A 'true' expression. 
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class True implements Visitable<ExprVisitor<?>> {
  /** 
   * Call visitor.boolTrue().
   * @param visitor Visitor.
   **/
  public void accept(final ExprVisitor<?> visitor) {
    visitor.boolConst(true);
  }

}
