package mobius.bmlvcgen.bml.bmllib;

import static annot.io.Code.AND;
import static annot.io.Code.ARRAYLENGTH;
import static annot.io.Code.ARRAY_ACCESS;
import static annot.io.Code.BITWISEAND;
import static annot.io.Code.BITWISEOR;
import static annot.io.Code.BITWISEXOR;
import static annot.io.Code.COND_EXPR;
import static annot.io.Code.DIV;
import static annot.io.Code.EQ;
import static annot.io.Code.EQUIV;
import static annot.io.Code.FALSE;
import static annot.io.Code.FIELD_REF;
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
import static annot.io.Code.THIS;
import static annot.io.Code.TRUE;
import static annot.io.Code.USHR;

import java.util.ArrayList;
import java.util.List;

import mobius.bmlvcgen.bml.ExprVisitor;
import mobius.bmlvcgen.util.Visitable;
import annot.bcexpression.BCExpression;
import annot.bcexpression.ConditionalExpression;
import annot.bcexpression.FieldRef;
import annot.bcexpression.NumberLiteral;

/**
 * Wrapper for simple bmllib expressions.
 * An expression is considered simple if its
 * wrapper uses all subexpressions in wrapped 
 * form only.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 * @param <V> Type of visitors.
 */
public class SimpleExpr<V extends ExprVisitor<V>> 
    implements Visitable<V> {
  private final BCExpression expr;
  private final List<Visitable<V>> subExprs;
  
  /**
   * Constructor.
   * @param expr Expression to be wrapped.
   * @param factory Object used to wrap subexpressions.
   */
  public SimpleExpr(final BCExpression expr,
                    final ExprFactory<Visitable<V>> factory) {
    this.expr = expr;
    subExprs = new ArrayList<Visitable<V>>();
    for (final BCExpression sub : expr.getAllSubExpr()) {
      subExprs.add(factory.wrap(sub));
    }
  }

  //CHECKSTYLE:OFF
  /** {@inheritDoc} */
  public void accept(final V visitor) {
    switch (expr.getConnector()) {
      case AND:
        visitor.boolAnd(subExprs.get(0), subExprs.get(1));
        break;
      case ARRAY_ACCESS:
        visitor.arrayAccess(subExprs.get(0), 
                            subExprs.get(1));
        break;
      case ARRAYLENGTH:
        visitor.arrayLength(subExprs.get(0));
        break;
      case BITWISEAND:
        visitor.bitAnd(subExprs.get(0), subExprs.get(1));
        break;
      case BITWISEOR:
        visitor.bitOr(subExprs.get(0), subExprs.get(1));
        break;
      case BITWISEXOR:
        visitor.bitXor(subExprs.get(0), subExprs.get(1));
        break;
      case COND_EXPR:
        assert expr instanceof ConditionalExpression;
        visitor.cond(subExprs.get(0), 
                     subExprs.get(1), 
                     subExprs.get(2));
        break;
      case DIV:
        visitor.intDiv(subExprs.get(0), subExprs.get(1));
        break;
      case EQ:
        visitor.eq(subExprs.get(0), subExprs.get(1));
        break;
      case EQUIV:
        visitor.boolEquiv(subExprs.get(0), subExprs.get(1));
        break;
      case FALSE:
        visitor.boolConst(false);
        break;
      case FIELD_REF:
        assert expr instanceof FieldRef;
        visitor.getField(((FieldRef)expr).getName(), 
                         BmllibType.getInstance(expr.getType()));
        break;
      case GRT:
        visitor.gt(subExprs.get(0), subExprs.get(1));
        break;
      case GRTEQ:
        visitor.ge(subExprs.get(0), subExprs.get(1));
        break;
      case IMPLIES:
        visitor.boolImpl(subExprs.get(0), subExprs.get(1));
        break;
      case INT_LITERAL:
        assert expr instanceof NumberLiteral;
        visitor.intConst(((NumberLiteral)expr).getValue());
        break;
      case LESS:
        visitor.lt(subExprs.get(0), subExprs.get(1));
        break;
      case LESSEQ:
        visitor.le(subExprs.get(0), subExprs.get(1));
        break;
      case MINUS:
        visitor.minus(subExprs.get(0));
        break;
      case MULT:
        visitor.mul(subExprs.get(0), subExprs.get(1));
        break;
      case NEG:
        visitor.bitNeg(subExprs.get(0));
        break;
      case NOT:
        visitor.boolNot(subExprs.get(0));
        break;
      case NOTEQ:
        visitor.neq(subExprs.get(0), subExprs.get(1));
        break;
      case NOTEQUIV:
        visitor.boolInequiv(subExprs.get(0), subExprs.get(1));
        break;
      case NULL:
        visitor.constNull();
        break;
      case OR:
        visitor.boolOr(subExprs.get(0), subExprs.get(1));
        break;
      case PLUS:
        visitor.add(subExprs.get(0), subExprs.get(1));
        break;
      case REM:
        visitor.mod(subExprs.get(0), subExprs.get(1));
        break;
      case SHL:
        visitor.shl(subExprs.get(0), subExprs.get(1));
        break;
      case SHR:
        visitor.sar(subExprs.get(0), subExprs.get(1));
        break;
      case THIS:
        visitor.self();
        break;
      case TRUE:
        visitor.boolConst(true);
        break;
      case USHR:
        visitor.shr(subExprs.get(0), subExprs.get(1));
        break;
      case JAVA_TYPE: // TODO: Types
      default:
        throw new UnsupportedOperationException(
          "Unknown bml connector " + expr.getConnector()
        );    
    }
  }
  //CHECKSTYLE:ON
  
  
}
