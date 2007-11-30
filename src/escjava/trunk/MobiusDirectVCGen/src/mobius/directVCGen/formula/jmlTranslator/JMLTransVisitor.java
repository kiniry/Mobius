package mobius.directVCGen.formula.jmlTranslator;

import javafe.ast.BinaryExpr;
import javafe.ast.FieldAccess;
import javafe.ast.FormalParaDecl;
import javafe.ast.InstanceOfExpr;
import javafe.ast.LiteralExpr;
import javafe.ast.RoutineDecl;
import javafe.ast.ThisExpr;
import javafe.ast.UnaryExpr;
import javafe.ast.VarDeclStmt;
import javafe.ast.VariableAccess;
import mobius.directVCGen.formula.Bool;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.formula.Num;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.formula.Type;
import mobius.directVCGen.formula.annotation.Set;
import mobius.directVCGen.formula.jmlTranslator.struct.ContextProperties;
import mobius.directVCGen.formula.jmlTranslator.struct.MethodProperties;
import mobius.directVCGen.vcgen.struct.Post;
import escjava.ast.ExprDeclPragma;
import escjava.ast.ExprModifierPragma;
import escjava.ast.NaryExpr;
import escjava.ast.QuantifiedExpr;
import escjava.ast.ResExpr;
import escjava.ast.TagConstants;
import escjava.ast.VarExprModifierPragma;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

public class JMLTransVisitor extends JmlVisitor {
  
  /** Reference to JML Expression Translator. */
  private final JmlExprToFormula fTranslator;
  
  /**
   * Visitor that translates JML Constructs to FOL by using JmlExprToFormula to
   * translate expressions.
   */
  public JMLTransVisitor() {
    this(false);
     
  }

  /**
   * Visitor that translates JML Constructs to FOL by using JmlExprToFormula to
   * translate expressions.
   * @param doSubsetChecking if the subset checking has to be done
   */
  public JMLTransVisitor(final boolean doSubsetChecking) {
    super(doSubsetChecking, null);
    fTranslator = new JmlExprToFormula(this);
     
  }


  @Override
  public final Object visitFormalParaDecl(final /*@non_null*/ FormalParaDecl x, 
                                          final Object o) {
    return fTranslator.genericVarDecl(x, o);
  }
  
  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitLiteralExpr(javafe.ast.LiteralExpr, java.lang.Object)
   */
  @Override
  public final Object visitLiteralExpr(final /*@non_null*/ LiteralExpr x, final Object o) {
    return fTranslator.literal(x, o);
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitVariableAccess(javafe.ast.VariableAccess, java.lang.Object)
   */
  @Override
  public final Object visitVariableAccess(final /*@non_null*/ VariableAccess x, final Object o) {
    return fTranslator.variableAccess(x, o);

  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitFieldAccess(javafe.ast.FieldAccess, java.lang.Object)
   */
  @Override
  public final Object visitFieldAccess(final /*@non_null*/ FieldAccess x, final Object o) {
    return fTranslator.fieldAccess(x, o);
  }
  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNaryExpr(escjava.ast.NaryExpr, java.lang.Object)
   */
  @Override
  public final Object visitNaryExpr(final /*@non_null*/ NaryExpr x, final Object o) {
    final ContextProperties prop = (ContextProperties) o;
    Term res = null;
    if (x.op == TagConstants.PRE) {
      res = fTranslator.oldExpr(x, prop);
    }
    else if (x.op == TagConstants.FRESH) {
      res = fTranslator.freshExpr(x, prop);
    }
    else if (x.op == TagConstants.TYPEOF) {
      final Term exprTerm = (Term) visitGCExpr(x, prop);
      res = Type.of(Heap.var, exprTerm);
    }
    else {
      res = (Term) visitGCExpr(x, o);
    }
    return res;
  }
    
  

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitInstanceOfExpr(javafe.ast.InstanceOfExpr, java.lang.Object)
   */
  @Override
  public final Object visitInstanceOfExpr(final /*@non_null*/ InstanceOfExpr x, final Object o) {
    return fTranslator.instanceOfExpr(x, o);
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitThisExpr(javafe.ast.ThisExpr, java.lang.Object)
   */
  @Override
  public final Object visitThisExpr(final /*@non_null*/ ThisExpr x, final Object o) {
    return fTranslator.thisLiteral(x, o);
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitResExpr(escjava.ast.ResExpr, java.lang.Object)
   */
  @Override
  public final Object visitResExpr(final /*@non_null*/ ResExpr x, final Object o) {
    final MethodProperties prop = (MethodProperties) o;
    return fTranslator.resultLiteral(x, prop);
  }
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitExprDeclPragma(escjava.ast.ExprDeclPragma, java.lang.Object)
   */
  @Override
  public final Object visitExprDeclPragma(final /*@non_null*/ ExprDeclPragma x, final Object o) {
    
    Term t;
    final ContextProperties cprop = (ContextProperties) o;
    
    if (x.tag == TagConstants.INITIALLY) {
      
      // to collect all fields in initially to do the subset check
      //fGlobal.put("doSubsetChecking", Boolean.TRUE);
      System.out.println(x.expr);
      final Term initiallyFOL = (Term) x.expr.accept(this, o);
      //fGlobal.put("doSubsetChecking", Boolean.FALSE);
      t = initiallyFOL;

      if (o instanceof MethodProperties) {
        final MethodProperties prop = (MethodProperties) o;
        final boolean initIsValid = doSubsetChecking(prop);
        if (initIsValid) {
          t = Logic.Safe.and(t, (Term) prop.get("initiallyFOL"));
          ((MethodProperties) o).put("initiallyFOL", t);
        }
        else {
          System.out.println("Initially error (subset check)! " +
              "The following term was not conjoined to the " +
              "overall type initially term: " + initiallyFOL.toString() + "\n");
        }
      }
    }
    else if (x.tag == TagConstants.INVARIANT) { 
      //fGlobal.put("doSubsetChecking", Boolean.TRUE);
      t = (Term) x.expr.accept(this, o);
      //fGlobal.put("doSubsetChecking", Boolean.FALSE);
      addToInv(x, t, cprop);
    }
    else if (x.tag == TagConstants.CONSTRAINT) {
      //fGlobal.put("doSubsetChecking", Boolean.TRUE); 
      t = (Term) x.expr.accept(this, o);
      //fGlobal.put("doSubsetChecking", Boolean.FALSE);
      constrToConstraints(x, t, cprop);
    }
    return null;
  }
  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitBinaryExpr(javafe.ast.BinaryExpr, java.lang.Object)
   */
  @Override
  public final Object visitBinaryExpr(final /*@non_null*/ BinaryExpr expr, 
                                      final Object o) {
    final ContextProperties prop = (ContextProperties) o;
    switch(expr.op) {
      case TagConstants.EQ: 
        return this.fTranslator.eq(expr, prop);
      case TagConstants.OR: 
        return this.fTranslator.or(expr, prop);
      case TagConstants.AND: 
        return this.fTranslator.and(expr, prop);
      case TagConstants.NE:
        return this.fTranslator.ne(expr, prop);
      case TagConstants.GE: 
        return this.fTranslator.ge(expr, prop);
      case TagConstants.GT: 
        return this.fTranslator.gt(expr, prop);
      case TagConstants.LE: 
        return this.fTranslator.le(expr, prop);
      case TagConstants.LT:  
        return this.fTranslator.lt(expr, prop);
      case TagConstants.BITOR: 
        return this.fTranslator.bitor(expr, prop);
      case TagConstants.BITXOR: 
        return this.fTranslator.bitxor(expr, prop);
      case TagConstants.BITAND: 
        return this.fTranslator.bitand(expr, prop);
      case TagConstants.LSHIFT:
        return this.fTranslator.lshift(expr, prop);
      case TagConstants.RSHIFT: 
        return this.fTranslator.rshift(expr, prop);
      case TagConstants.URSHIFT:
        return this.fTranslator.urshift(expr, prop);
      case TagConstants.ADD: 
        return this.fTranslator.add(expr, prop);
      case TagConstants.SUB: 
        return this.fTranslator.sub(expr, prop);
      case TagConstants.DIV: 
        return this.fTranslator.div(expr, prop);
      case TagConstants.MOD: 
        return this.fTranslator.mod(expr, prop);
      case TagConstants.STAR: 
        return this.fTranslator.star(expr, prop);
      case TagConstants.ASSIGN:
        return this.fTranslator.assign(expr, prop);
      case TagConstants.ASGMUL: 
        return this.fTranslator.asgmul(expr, prop);
      case TagConstants.ASGDIV: 
        return this.fTranslator.asgdiv(expr, prop);
      case TagConstants.ASGREM: 
        return this.fTranslator.asgrem(expr, prop);
      case TagConstants.ASGADD: 
        return this.fTranslator.asgadd(expr, prop);
      case TagConstants.ASGSUB: 
        return this.fTranslator.asgsub(expr, prop);
      case TagConstants.ASGLSHIFT: 
        return this.fTranslator.asglshift(expr, prop);
      case TagConstants.ASGRSHIFT: 
        return this.fTranslator.asgrshift(expr, prop);
      case TagConstants.ASGURSHIFT: 
        return this.fTranslator.asgurshif(expr, prop);
      case TagConstants.ASGBITAND: 
        return this.fTranslator.asgbitand(expr, prop);
        // jml specific operators 
      case TagConstants.IMPLIES: 
        return this.fTranslator.implies(expr, prop);
      case TagConstants.EXPLIES:
        return this.fTranslator.explies(expr, prop);
      case TagConstants.IFF: // equivalence (equality)
        return this.fTranslator.iff(expr, prop);
      case TagConstants.NIFF:    // discrepance (xor)
        return this.fTranslator.niff(expr, prop);
      case TagConstants.SUBTYPE: 
        return this.fTranslator.subtype(expr, prop);
      case TagConstants.DOTDOT: 
        return this.fTranslator.dotdot(expr, prop);

      default:
        throw new IllegalArgumentException("Unknown construct :" +
                                           TagConstants.toString(expr.op) +
                                           " " +  expr);
    }

  }
  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitVarExprModifierPragma(escjava.ast.VarExprModifierPragma, java.lang.Object)
   */
  @Override
  public final Object visitVarExprModifierPragma(final /*@non_null*/ VarExprModifierPragma x, 
                                                 final Object o) {
    final MethodProperties prop = (MethodProperties) o;
    
    final RoutineDecl currentRoutine = prop.getDecl();
    final Post allExPosts = Lookup.getExceptionalPostcondition(currentRoutine);
    final QuantVariableRef commonExceptionVar = allExPosts.getRVar();

    final Term typeOfException = Type.translateToType(x.arg.type);
    final QuantVariableRef newExceptionVar = Expression.rvar(x.arg);

    Term newExPost = (Term)x.expr.accept(this, o);
    newExPost = newExPost.subst(newExceptionVar, commonExceptionVar);
    final Term guard = Logic.assignCompat(Heap.var, commonExceptionVar, typeOfException);
    final Post result = new Post (commonExceptionVar, Logic.Safe.implies(guard, newExPost));
    Lookup.addExceptionalPostcondition(prop.getDecl(), result);
    return null;
  }
  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitExprModifierPragma(escjava.ast.ExprModifierPragma, java.lang.Object)
   */
  @Override
  public final Object visitExprModifierPragma(final /*@non_null*/ ExprModifierPragma x, 
                                              final Object o) {
    final MethodProperties prop = (MethodProperties)o;

    Term t = (Term)visitASTNode(x, o);
    if (t.getSort().equals(Heap.sortValue)) {
      t = Bool.value(true);
    }
    t = Logic.boolToPred(t);
    switch (x.getTag()) {
      case TagConstants.REQUIRES:
        //addToPrecondition(t, o);
        Lookup.addPrecondition(prop.getDecl(), t);
        break;
      case TagConstants.ENSURES:
      case TagConstants.POSTCONDITION:
      case TagConstants.POSTCONDITION_REDUNDANTLY:
        //addToPostcondition(t, o);
        Lookup.addNormalPostcondition(prop, t);
        break;
      default:
        break;
    }
    return null;
  }
  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitVarDeclStmt(javafe.ast.VarDeclStmt, java.lang.Object)
   */
  @Override
  public final Object visitVarDeclStmt(final /*@non_null*/ VarDeclStmt x, final Object o) {
    //final MethodProperties prop = (MethodProperties) o;


    //It's only called if we have a ghost variable declaration with maybe a set stmt
    final Set ghostVar = new Set();
    if (x.decl.init != null) {
      ghostVar.assignment = new Set.Assignment(Expression.rvar(x.decl),
                                               (Term) x.decl.init.accept(this, o));
    }
    ghostVar.declaration = Expression.rvar(x.decl); 
    return ghostVar;
  }
  
  public /*@non_null*/ Object visitQuantifiedExpr(final /*@non_null*/ QuantifiedExpr x, 
                                                  final Object o) {
    return fTranslator.quantifier(x, o);
  }
  
  
  public /*@non_null*/ Object visitUnaryExpr(final /*@non_null*/ UnaryExpr x, 
                                             final Object o) {
    Term res = (Term) visitExpr(x, o);
    switch (x.op) {
      case TagConstants.UNARYSUB:
        res = Num.sub(res);
        break;
      case TagConstants.NOT:
        if (res.getSort().equals(Bool.sort)) {
          res = Bool.not(res);
        }
        else {
          if (res.getSort().equals(Heap.sortValue)) {
            System.out.println(res);
            System.out.println(TagConstants.toString(x.op));
            res = Ref.nullValue();
          }
        }
      default:
        break;
    }
    
    return res;
  }
}
