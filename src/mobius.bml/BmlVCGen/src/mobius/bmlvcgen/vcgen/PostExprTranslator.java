package mobius.bmlvcgen.vcgen;

import mobius.bmlvcgen.bml.PostExprVisitor;
import mobius.bmlvcgen.bml.PreExprVisitor;
import mobius.bmlvcgen.util.Visitable;
import mobius.directvcgen.formula.Expression;
import mobius.directvcgen.formula.Type;

import org.apache.bcel.generic.ObjectType;

import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.NodeBuilder.Sort;

/**
 * Translator for postconditions.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class PostExprTranslator 
  extends ExprTranslator<PostExprVisitor> 
  implements PostExprVisitor {

  // Type of method result.
  private final org.apache.bcel.generic.Type resultType;
  
  // Object used to translate old expressions.
  private final PreExprTranslator preTrans;
  
  // Method result.
  private final QuantVariable resultVar;
  
  /**
   * Constructor.
   * @param thisType Type of 'this' object.
   * @param resultType Type of method result.
   * @param resultVar A variable which will hold method result.
   */
  public PostExprTranslator(
      final ObjectType thisType,
      final org.apache.bcel.generic.Type resultType,
      final QuantVariable resultVar) {
    super(thisType, false); // old = false
    this.resultType = resultType;
    preTrans = new PreExprTranslator(thisType, true);
    this.resultVar = resultVar;
  }
  
  /** {@inheritDoc} */
  @Override
  protected PostExprVisitor getThis() {
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
    setLastExpr(Expression.rvar(var));
    setLastType(tc.getType());
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super PreExprVisitor>> 
  void old(final Expr expr) {
    expr.accept(preTrans);
    setLastExpr(preTrans.getLastExpr());
    setLastType(preTrans.getLastType());
  }

  /** {@inheritDoc} */
  public void result() {
    setLastExpr(Expression.rvar(resultVar));
    setLastType(resultType);
  }
}
