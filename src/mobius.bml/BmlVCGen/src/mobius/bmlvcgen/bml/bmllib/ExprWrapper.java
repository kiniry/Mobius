package mobius.bmlvcgen.bml.bmllib;

import static annot.io.Code.AND;
import static annot.io.Code.ARRAYLENGTH;
import static annot.io.Code.ARRAY_ACCESS;
import static annot.io.Code.BITWISEAND;
import static annot.io.Code.BITWISEOR;
import static annot.io.Code.BITWISEXOR;
import static annot.io.Code.BOUND_VAR;
import static annot.io.Code.COND_EXPR;
import static annot.io.Code.DIV;
import static annot.io.Code.EQ;
import static annot.io.Code.EQUIV;
import static annot.io.Code.EXISTS;
import static annot.io.Code.EXISTS_WITH_NAME;
import static annot.io.Code.EXPRESSION_ROOT;
import static annot.io.Code.FALSE;
import static annot.io.Code.FIELD_ACCESS;
import static annot.io.Code.FIELD_REF;
import static annot.io.Code.FORALL;
import static annot.io.Code.FORALL_WITH_NAME;
import static annot.io.Code.GRT;
import static annot.io.Code.GRTEQ;
import static annot.io.Code.IMPLIES;
import static annot.io.Code.INT_LITERAL;
import static annot.io.Code.JAVA_TYPE;
import static annot.io.Code.LESS;
import static annot.io.Code.LESSEQ;
import static annot.io.Code.MINUS;
import static annot.io.Code.MULT;
import static annot.io.Code.NEG;
import static annot.io.Code.NOT;
import static annot.io.Code.NOTEQ;
import static annot.io.Code.NOTEQUIV;
import static annot.io.Code.NULL;
import static annot.io.Code.OR;
import static annot.io.Code.PLUS;
import static annot.io.Code.REM;
import static annot.io.Code.SHL;
import static annot.io.Code.SHR;
import static annot.io.Code.SINGLE_OCCURENCE;
import static annot.io.Code.THIS;
import static annot.io.Code.TRUE;
import static annot.io.Code.USHR;
import mobius.bmlvcgen.bml.ExprVisitor;
import mobius.bmlvcgen.util.Visitable;
import annot.bcexpression.BCExpression;
import annot.bcexpression.BoundVar;
import annot.bcexpression.FieldAccess;
import annot.bcexpression.SingleOccurence;
import annot.bcexpression.formula.QuantifiedFormula;

/**
 * This class creates wrappers for bmllib expressions.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 * @param <V> Type of visitors.
 */
public class ExprWrapper<V extends ExprVisitor<V>> 
    implements ExprFactory<Visitable<V>> {
  
  /**
   * Remove all expression roots, single occurences and
   * other strange things from head of an expression.
   * @param e Expression.
   * @return Unpacked expression.
   */
  protected static BCExpression unpack(final BCExpression e) {
    if (e.getConnector() == EXPRESSION_ROOT) {
      return unpack(e.getSubExpr(0));
    } else if (e.getConnector() == SINGLE_OCCURENCE) {
      return unpack(((SingleOccurence)e).getSharedExpr());
    } else {
      return e;
    }
  }
  
  //CHECKSTYLE:OFF
  /** {@inheritDoc} */
  public Visitable<V> wrap(final BCExpression expression) {
    final BCExpression expr = unpack(expression);
    switch (expr.getConnector()) {
      case AND:
      case ARRAY_ACCESS:
      case ARRAYLENGTH:
      case BITWISEAND:
      case BITWISEOR:
      case BITWISEXOR:
      case COND_EXPR:
      case DIV:
      case EQ:
      case EQUIV:
      case FALSE:
      case FIELD_REF:
      case GRT:
      case GRTEQ:
      case IMPLIES:
      case INT_LITERAL:
      case LESS:
      case LESSEQ:
      case MINUS:
      case MULT:
      case NEG:
      case NOT:
      case NOTEQ:
      case NOTEQUIV:
      case NULL:
      case OR:
      case PLUS:
      case REM:
      case SHL:
      case SHR:
      case THIS:
      case TRUE:
      case USHR:
      case JAVA_TYPE:
        return new SimpleExpr<V>(expr, this);
      case BOUND_VAR:
        return new BoundVarExpr<V>((BoundVar)expr);
      case FIELD_ACCESS:
        return new FieldAccessExpr<V>((FieldAccess)expr, this);
      case FORALL:
      case FORALL_WITH_NAME:
      case EXISTS:
      case EXISTS_WITH_NAME:
        return new QuantifiedExpr<V>(
            (QuantifiedFormula)expr, 
            0, 
            this
        );
      default:
        throw new UnsupportedOperationException(
          "Unknown bml connector " + expr.getConnector()
        );    
    }
  }
  //CHECKSTYLE:ON
}
