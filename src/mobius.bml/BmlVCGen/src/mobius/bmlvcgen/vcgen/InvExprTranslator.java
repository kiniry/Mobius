package mobius.bmlvcgen.vcgen;

import mobius.bmlvcgen.bml.InvExprVisitor;

import org.apache.bcel.generic.ObjectType;

/**
 * Translator for invariant expressions.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class InvExprTranslator 
  extends ExprTranslator<InvExprVisitor> 
  implements InvExprVisitor {

  /**
   * Constructor.
   * @param thisType Type of 'this' object.
   */
  public InvExprTranslator(final ObjectType thisType) {
    super(thisType, false); // old = false
  }
  
  /** {@inheritDoc} */
  @Override
  protected InvExprVisitor getThis() {
    return this;
  }

}
