package mobius.bmlvcgen.vcgen;

import mobius.bmlvcgen.bml.PreExprVisitor;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Type;

import org.apache.bcel.generic.ObjectType;

import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.NodeBuilder.Sort;

/**
 * Translator for invariant expressions.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class PreExprTranslator 
  extends ExprTranslator<PreExprVisitor> 
  implements PreExprVisitor {

  /**
   * Constructor.
   * @param thisType Type of 'this' object.
   */
  public PreExprTranslator(final ObjectType thisType) {
    super(thisType, false); // old = false
  }

  /**
   * Constructor.
   * @param thisType Type of 'this' object.
   * @param old Is the expression inside '\\old' ?
   */
  public PreExprTranslator(final ObjectType thisType,
                           final boolean old) {
    super(thisType, old);
  }
  
  /** {@inheritDoc} */
  @Override
  protected PreExprVisitor getThis() {
    return this;
  }

  /** {@inheritDoc} */
  public void arg(final int i, 
                  final String name, 
                  final mobius.bmlvcgen.bml.types.Type type) {
    final String varName = 
      BmlAnnotationGenerator.localVarName(i, name);
    final TypeConverter tc = getTypeConverter();
    type.accept(tc);
    final Sort sort = Type.getSort(tc.getType());
    final QuantVariable var = Expression.var(varName, sort);
    if (isOld()) {
      setLastExpr(Expression.rvar(Expression.old(var)));
    } else {
      setLastExpr(Expression.rvar(var));
    }
    setLastType(tc.getType());
  }
}
