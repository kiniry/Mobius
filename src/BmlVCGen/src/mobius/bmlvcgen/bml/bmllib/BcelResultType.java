package mobius.bmlvcgen.bml.bmllib;

import mobius.bmlvcgen.bml.types.ResultType;
import mobius.bmlvcgen.bml.types.ResultTypeVisitor;

import org.apache.bcel.Constants;
import org.apache.bcel.generic.Type;

/**
 * ResultType wrapper for BCEL types.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class BcelResultType extends BcelType implements ResultType {
  /**
   * Constructor.
   * @param type Type to be wrapped.
   */
  protected BcelResultType(final Type type) {
    super(type);
  }

  /**
   * Factory method.
   * @param type Type to be wrapped.
   * @return BmllibType instance.
   */
  public static BcelResultType getInstance(final Type type) {
    // TODO: cache types.
    return new BcelResultType(type);
  }
  
  /** {@inheritDoc} */
  public void accept(final ResultTypeVisitor v) {
    if (getType().getType() == Constants.T_VOID) { // :-(
      v.visitVoid();
    } else {
      super.accept(v);
    }
  }
}
