package mobius.bmlvcgen.vcgen;

import mobius.bmlvcgen.bml.AssertExprVisitor;
import mobius.bmlvcgen.bml.PreExprVisitor;
import mobius.bmlvcgen.util.Visitable;
import mobius.directvcgen.formula.Expression;
import mobius.directvcgen.formula.Type;

import org.apache.bcel.generic.ObjectType;

import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.NodeBuilder.Sort;

/**
 * Translator for assert expressions.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class AssertExprTranslator 
  extends ExprTranslator<AssertExprVisitor> 
  implements AssertExprVisitor {
  
  // Object used to translate old expressions.
  private final PreExprTranslator preTrans;
  
  /**
   * Constructor.
   * @param thisType Type of 'this' object.
   */
  public AssertExprTranslator(
      final ObjectType thisType) {
    super(thisType, false); // old = false
    preTrans = new PreExprTranslator(thisType, true);
  }
  
  /** {@inheritDoc} */
  @Override
  protected AssertExprVisitor getThis() {
    return this;
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super PreExprVisitor>> 
  void aold(final Expr expr) {
    expr.accept(preTrans);
    setLastExpr(preTrans.getLastExpr());
    setLastType(preTrans.getLastType());
  }
  
  /** {@inheritDoc} */
  public void local(final int i, 
                  final String name, 
                  final mobius.bmlvcgen.bml.types.Type type) {
    final String varName = 
      BmlAnnotationGenerator.localVarName(i, name);
    final TypeConverter tc = getTypeConverter();
    type.accept(tc);
    final Sort sort = Type.getSort(tc.getType());
    final QuantVariable var = Expression.var(varName, sort);
    setLastExpr(Expression.rvar(var));
    setLastType(tc.getType());
  }

}
