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
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Num;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.formula.Type;
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



  @Override
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
  @Override
  public Object visitLiteralExpr(final LiteralExpr expr,  final Object o) {
    final VCEntry vce = (VCEntry) o;
    final Post result = vce.fPost;
    Term term = null;
    int val;

    final Term intMin = Num.value(Integer.MIN_VALUE);
    final Term intMax = Num.value(Integer.MAX_VALUE);
    // System out.println(TagConstants.toString(expr.tag));
    switch (expr.tag) {
      case TagConstants.BOOLEANLIT:
        // -2^31 <= z < 2^31 
        if ((Boolean)expr.value) {
          val = 1;// Num.value(1); 
        }
        else {
          val = 0; //Num.value(0); 
        }
        final QuantVariableRef ival = Expression.rvar("Ival", Type.sort);
        Term vval = Heap.sortToValue(Num.value(val));
        final Term compat = Expression.sym("compat_ValKind_value", new Term[] {ival, vval});
        
        term =  Logic.implies (Expression.sym("(Int.range " + val + ")", new Term [] {}),
                     Logic.implies(Logic.assignCompat(Heap.var, vval, 
                                                      Expression.rvar("(PrimitiveType BOOLEAN)", 
                                                                     Type.sort)),
                         Logic.implies(compat, result.nonSafeSubst(result.getRVar(), vval))));
        
        break;
      case TagConstants.INTLIT:
        //-2^31 <= z < 2^31 
        val = (Integer)expr.value;
//        term = result.substWith(val);
        term = Logic.implies (Expression.sym("(Int.range " + val + ")", new Term[]{}),
                              result.substWith(Num.value(val)));
        break;
      case TagConstants.LONGLIT:
        term = result.substWith(Num.value((Long)expr.value));
        break;
      case TagConstants.BYTELIT:
        //-2^7  <= z < 2^7
//        val = Num.value((Byte)expr.value);
//        final Term byteMin = Num.value(Byte.MIN_VALUE);
//        final Term byteMax = Num.value(Byte.MAX_VALUE);
//        term = Logic.implies (Expression.sym("Byte.range", new Term[] {val}),
//                              result.substWith(val));
        break;
      case TagConstants.SHORTLIT:
        //-2^15 <= z < 2^15 
//        val = Num.value((Short)expr.value);
//        final Term shortMin = Num.value(Short.MIN_VALUE);
//        final Term shortMax = Num.value(Short.MAX_VALUE);
//        term = Logic.implies (Expression.sym("Short.range", new Term[] {val}),
//                              result.substWith(val));
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
    return new Post(result.getRVar(), term);
  }

  /*
   * (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitUnaryExpr(javafe.ast.UnaryExpr, java.lang.Object)
   */
  @Override
  public Object visitUnaryExpr(final UnaryExpr expr, final Object o) {
    final VCEntry post = (VCEntry) o;
    switch(expr.op) {
      case TagConstants.UNARYADD:
        // for the unary add we do nothing
        return post.fPost;
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
  @Override
  public /*@non_null*/ Object visitThisExpr(final /*@non_null*/ ThisExpr x, final Object o) {
    final VCEntry vce = (VCEntry) o;
    return new Post(vce.fPost.substWith(Ref.varThis)); // variable particuliere
  }

  /**
   * We just get what is contained inside the paren expression.
   */
  @Override
  public /*@non_null*/ Object visitParenExpr(final /*@non_null*/ ParenExpr x, final Object o) {
    return fVcg.getPre(x.expr, (VCEntry) o);
  }

  @Override
  public /*@non_null*/ Object visitMethodInvocation(final /*@non_null*/ MethodInvocation x, 
                                                    final Object o) {
    return fVcg.methodInvocation(x, (VCEntry) o);
  }

  @Override
  public /*@non_null*/ Object visitExpr(final /*@non_null*/ Expr x, final Object o) {
    throw new IllegalArgumentException("Illegal expr!!!!");
  }
  
  @Override
  public /*@non_null*/ Object visitInstanceOfExpr(final /*@non_null*/ InstanceOfExpr x, 
                                                  final Object o) {
    return fVcg.instanceOf(x, (VCEntry) o);
  }
  
  @Override
  public /*@non_null*/ Object visitCondExpr(final /*@non_null*/ CondExpr x, final Object o) {
    return fVcg.condExpr(x, (VCEntry) o);
  }

  @Override
  public /*@non_null*/ Object visitCastExpr(final /*@non_null*/ CastExpr x, final Object o) {
    return fVcg.castExpr(x, (VCEntry) o);
  }


  @Override
  public Object visitVariableAccess(final VariableAccess m, final Object o) {
    final VCEntry res = (VCEntry) o;
    final Term v = Expression.rvar(m.decl);
    return  new Post(res.fPost.substWith(v));
  }

  @Override
  public /*@non_null*/ Object visitFieldAccess(final /*@non_null*/ FieldAccess x, 
                                               final Object o) {
    return fVcg.fieldAccess(x, (VCEntry) o);
  }

  @Override
  public /*@non_null*/ Object visitNewInstanceExpr(final /*@non_null*/ NewInstanceExpr x, 
                                                   final Object o) {
    return fVcg.newInstance(x, (VCEntry) o);
  }
  
  @Override
  public /*@non_null*/ Object visitObjectDesignator(final /*@non_null*/ ObjectDesignator od, 
                                                    final Object vce) {
    return fVcg.objectDesignator(od, (VCEntry) vce);
  }


  @Override
  public /*@non_null*/ Object visitVarInit(final /*@non_null*/ VarInit x, final Object o) {
    return illegalExpr(x, o);
  }

  @Override
  public /*@non_null*/ Object visitArrayInit(final /*@non_null*/ ArrayInit init, 
                                             final Object o) {
    return fVcg.arrayInit(init, (VCEntry) o);
  }

  @Override
  public /*@non_null*/ Object visitArrayRefExpr(final /*@non_null*/ ArrayRefExpr x, 
                                                final Object o) {
    return fVcg.arrayRef(x, (VCEntry)o);
  }
  
  @Override
  public /*@non_null*/ Object visitNewArrayExpr(final /*@non_null*/ NewArrayExpr x, 
                                                final Object o) {
    return fVcg.newArray(x, (VCEntry) o);
  }

  @Override
  public /*@non_null*/ Object visitAmbiguousVariableAccess(final /*@non_null*/ 
                                                           AmbiguousVariableAccess x, 
                                                           final Object o) {
    return visitExpr(x, o);
  }

  @Override
  public /*@non_null*/ Object visitAmbiguousMethodInvocation(final /*@non_null*/ 
                                                             AmbiguousMethodInvocation x, 
                                                             final Object o) {
    return visitExpr(x, o);
  }

}
