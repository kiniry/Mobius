package mobius.directVCGen.vcgen.expression;

import javafe.ast.AmbiguousMethodInvocation;
import javafe.ast.AmbiguousVariableAccess;
import javafe.ast.ArrayInit;
import javafe.ast.ArrayRefExpr;
import javafe.ast.BinaryExpr;
import javafe.ast.CastExpr;
import javafe.ast.CondExpr;
import javafe.ast.Expr;
import javafe.ast.FieldAccess;
import javafe.ast.InstanceOfExpr;
import javafe.ast.LiteralExpr;
import javafe.ast.MethodInvocation;
import javafe.ast.NewArrayExpr;
import javafe.ast.NewInstanceExpr;
import javafe.ast.ObjectDesignator;
import javafe.ast.ParenExpr;
import javafe.ast.ThisExpr;
import javafe.ast.UnaryExpr;
import javafe.ast.VarInit;
import javafe.ast.VariableAccess;
import mobius.directVCGen.formula.Bool;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Num;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.vcgen.ABasicVisitor;
import mobius.directVCGen.vcgen.struct.Post;
import mobius.directVCGen.vcgen.struct.VCEntry;
import escjava.ast.TagConstants;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

public class ExpressionVisitor extends ABasicVisitor {
  /** the expression vcgen associated to the visitor. */
  private final ExpressionVCGen fVcg;

  /**
   * The default constructor.
   */
  public ExpressionVisitor() {
    fVcg = new ExpressionVCGen(this);
  }




  public Object visitBinaryExpr(final BinaryExpr expr, final Object o) {

    //System out.println(TagConstants.toString(expr.op));
    final VCEntry post = (VCEntry) o;
    switch(expr.op) {
      case TagConstants.EQ:
      case TagConstants.OR:
      case TagConstants.AND:
      case TagConstants.NE:
      case TagConstants.GE:
      case TagConstants.GT:
      case TagConstants.LE:
      case TagConstants.LT:
      case TagConstants.BITOR:
      case TagConstants.BITXOR:
      case TagConstants.BITAND:
      case TagConstants.LSHIFT:
      case TagConstants.RSHIFT:
      case TagConstants.URSHIFT:
      case TagConstants.ADD:
      case TagConstants.SUB:
      case TagConstants.STAR:
        return fVcg.stdBinExpression(expr.op, expr.left, expr.right, post);


      case TagConstants.DIV:
      case TagConstants.MOD:
        return fVcg.stdBinExpression(expr.op, expr.left, expr.right, post);
  
  
      case TagConstants.ASSIGN:
        return fVcg.assign(expr, post);
      case TagConstants.ASGMUL:
      case TagConstants.ASGDIV:
      case TagConstants.ASGREM:
      case TagConstants.ASGADD:
      case TagConstants.ASGSUB:
      case TagConstants.ASGLSHIFT:
      case TagConstants.ASGRSHIFT:
      case TagConstants.ASGURSHIFT:
      case TagConstants.ASGBITAND:
      case TagConstants.ASGBITOR:
      case TagConstants.ASGBITXOR:
        return fVcg.assignSpecial(expr, post);
  
        // jml specific operators
      case TagConstants.IMPLIES:
      case TagConstants.EXPLIES:
      case TagConstants.IFF: 
      case TagConstants.NIFF:
      case TagConstants.SUBTYPE:
      case TagConstants.DOTDOT:
        throw new IllegalArgumentException("Unmanaged construct :" +
                                           TagConstants.toString(expr.op) + " " +  expr);
      default:
        throw new IllegalArgumentException("Unknown construct :" +
                                           TagConstants.toString(expr.op) + " " +  expr);
    }
  }


  // TODO: add comments
  public Object visitLiteralExpr(LiteralExpr expr,  Object o) {
    final VCEntry vce = (VCEntry) o;
    final Post result = vce.post;
    Term term = null;
    // System out.println(TagConstants.toString(expr.tag));
    switch (expr.tag) {
      case TagConstants.BOOLEANLIT:
        term = result.substWith(Bool.value((Boolean)expr.value));
        break;
      case TagConstants.INTLIT:
        term = result.substWith(Num.value((Integer)expr.value));
        break;
      case TagConstants.LONGLIT:
        term = result.substWith(Num.value((Long)expr.value));
        break;
      case TagConstants.BYTELIT:
        result.substWith(Num.value((Byte)expr.value));
        break;
      case TagConstants.SHORTLIT: 
        term = result.substWith(Num.value((Short)expr.value));
        break;
      case TagConstants.FLOATLIT:
        term = result.substWith(Num.value((Float)expr.value));
        break;
      case TagConstants.CHARLIT:
        result.substWith(Num.value((Character)expr.value));
        break;
      case TagConstants.DOUBLELIT:
        term = result.substWith(Num.value((Double)expr.value));
        break;
      case TagConstants.STRINGLIT:
        term = result.substWith(Ref.strValue((String)expr.value));
        break;
      case TagConstants.NULLLIT:
        term = result.substWith(Ref.Null());
        break;
      default:
        throw new IllegalArgumentException("Unknown construct :" +
                                           TagConstants.toString(expr.tag) + " " +  expr);
    }
    return new Post(result.var, term);
  }

  /*
   * (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitUnaryExpr(javafe.ast.UnaryExpr, java.lang.Object)
   */
  public Object visitUnaryExpr(UnaryExpr expr, Object o) {
    final VCEntry post = (VCEntry) o;
    switch(expr.op) {
      case TagConstants.UNARYADD:
        // for the unary add we do nothing
        return post.post;
      case TagConstants.POSTFIXINC:
        return fVcg.postfixInc(expr, post);
      case TagConstants.INC:
        return fVcg.inc(expr, post);
      case TagConstants.POSTFIXDEC:
        return fVcg.postfixDec(expr, post);
      case TagConstants.DEC:
        return fVcg.dec(expr, post);
      case TagConstants.BITNOT:
        return fVcg.bitNot(expr, post);
      case TagConstants.UNARYSUB:
        return fVcg.unarySub(expr, post);
      case TagConstants.NOT:
        return fVcg.not(expr, post);
      default:
        throw new IllegalArgumentException("Unknown construct :" +
                                           TagConstants.toString(expr.op) + " " +  expr);
    }
  }

  /*
   * (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitThisExpr(javafe.ast.ThisExpr, java.lang.Object)
   */
  public /*@non_null*/ Object visitThisExpr(/*@non_null*/ ThisExpr x, Object o) {
    VCEntry vce = (VCEntry) o;
    return new Post(vce.post.substWith(Ref.varThis)); // variable particuliere
  }

  /**
   * We just get what is contained inside the paren expression.
   */
  public /*@non_null*/ Object visitParenExpr(/*@non_null*/ ParenExpr x, Object o) {
    return fVcg.getPre(x.expr, (VCEntry) o);
  }

  public /*@non_null*/ Object visitMethodInvocation(/*@non_null*/ MethodInvocation x, Object o) {
    return fVcg.methodInvocation(x, (VCEntry) o);
  }

  public /*@non_null*/ Object visitExpr(/*@non_null*/ Expr x, Object o) {
    throw new IllegalArgumentException("Illegal expr!!!!");
  }

  public /*@non_null*/ Object visitInstanceOfExpr(/*@non_null*/ InstanceOfExpr x, Object o) {
    return fVcg.instanceOf(x, (VCEntry) o);
  }

  public /*@non_null*/ Object visitCondExpr(/*@non_null*/ CondExpr x, Object o) {
    return fVcg.condExpr(x, (VCEntry) o);
  }


  public /*@non_null*/ Object visitCastExpr(/*@non_null*/ CastExpr x, Object o) {
    return fVcg.castExpr(x, (VCEntry) o);
  }



  public Object visitVariableAccess(VariableAccess m, Object o) {
    final VCEntry res = (VCEntry) o;
    final QuantVariableRef v = Expression.rvar(m.decl);
    return  new Post(res.post.substWith(v));
  }

  public /*@non_null*/ Object visitFieldAccess(/*@non_null*/ FieldAccess x, Object o) {
    return fVcg.fieldAccess(x, (VCEntry) o);
  }

  public /*@non_null*/ Object visitNewInstanceExpr(/*@non_null*/ NewInstanceExpr x, Object o) {
    return fVcg.newInstance(x, (VCEntry) o);
  }
  public /*@non_null*/ Object visitObjectDesignator(/*@non_null*/ ObjectDesignator od, Object vce) {
    return fVcg.objectDesignator(od, (VCEntry) vce);
  }



  public /*@non_null*/ Object visitVarInit(/*@non_null*/ VarInit x, Object o) {
    return illegalExpr(x, o);
  }

  public /*@non_null*/ Object visitArrayInit(/*@non_null*/ ArrayInit init, Object o) {
    return fVcg.arrayInit(init, (VCEntry) o);
  }

  public /*@non_null*/ Object visitArrayRefExpr(/*@non_null*/ ArrayRefExpr x, Object o) {
    return fVcg.arrayRef(x, (VCEntry)o);
  }
  public /*@non_null*/ Object visitNewArrayExpr(/*@non_null*/ NewArrayExpr x, Object o) {
    return fVcg.newArray(x, (VCEntry) o);
  }


  public /*@non_null*/ Object visitAmbiguousVariableAccess(/*@non_null*/ AmbiguousVariableAccess x, Object o) {
    return visitExpr(x, o);
  }

  public /*@non_null*/ Object visitAmbiguousMethodInvocation(/*@non_null*/ AmbiguousMethodInvocation x, Object o) {
    return visitExpr(x, o);
  }

}
