package mobius.bmlvcgen.bml.bmllib;

import mobius.bmlvcgen.bml.PostExprVisitor;
import mobius.bmlvcgen.bml.types.Type;
import mobius.bmlvcgen.util.Visitable;

/**
 * Wrapper for bmllib argument references in postconditions.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class PostArgExpr 
    implements Visitable<PostExprVisitor> {
  private final int index;
  private final String name;
  private final Type type;
  
  /**
   * Constructor.
   * @param index Argument index.
   * @param name Argument name (possibly null).
   * @param type Argument type.
   */
  public PostArgExpr(final int index, 
                           final String name,
                           final Type type) {
    this.index = index;
    this.name = name;
    this.type = type;
  }

  /** {@inheritDoc} */
  public void accept(final PostExprVisitor visitor) {
    visitor.arg(index, name, type);
  }
}
