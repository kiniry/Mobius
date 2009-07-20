package mobius.directvcgen.translator;

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
import mobius.directVCGen.formula.Num;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.formula.Type;
import mobius.directVCGen.formula.annotation.Set;
import mobius.directvcgen.translator.struct.ContextProperties;
import mobius.directvcgen.translator.struct.MethodProperties;
import mobius.directvcgen.vcgen.struct.Post;
import escjava.ast.ExprDeclPragma;
import escjava.ast.ExprModifierPragma;
import escjava.ast.NaryExpr;
import escjava.ast.QuantifiedExpr;
import escjava.ast.ResExpr;
import escjava.ast.TagConstants;
import escjava.ast.VarExprModifierPragma;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

class JMLTransVisitor extends JmlVisitor {
  
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

  /** {@inheritDoc} */
  @Override
  public final Object visitFormalParaDecl(final /*@non_null*/ FormalParaDecl x, 
                                          final Object o) {
    return fTranslator.genericVarDecl(x, (ContextProperties) o);
  }
  

  /** {@inheritDoc} */
  @Override
  public final Object visitLiteralExpr(final /*@non_null*/ LiteralExpr x, final Object o) {
    return fTranslator.literal(x, (ContextProperties) o);
  }

  /** {@inheritDoc} */
  @Override
  public final Object visitVariableAccess(final /*@non_null*/ VariableAccess x, 
                                          final Object o) {
    return fTranslator.variableAccess(x, (ContextProperties) o);

  }
  
  /** {@inheritDoc} */
  @Override
  public final Object visitFieldAccess(final /*@non_null*/ FieldAccess x, final Object o) {
    return fTranslator.fieldAccess(x, (ContextProperties) o);
  }
  
  /** {@inheritDoc} */
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
    
  

  /** {@inheritDoc} */
  @Override
  public final Object visitInstanceOfExpr(final /*@non_null*/ InstanceOfExpr x, 
                                          final Object o) {
    return fTranslator.instanceOfExpr(x, (ContextProperties) o);
  }

  /** {@inheritDoc} */
  @Override
  public final Object visitThisExpr(final /*@non_null*/ ThisExpr x, final Object o) {
    return fTranslator.thisLiteral(x, (ContextProperties) o);
  }

  /** {@inheritDoc} */
  @Override
  public final Object visitResExpr(final /*@non_null*/ ResExpr x, final Object o) {
    final MethodProperties prop = (MethodProperties) o;
    return fTranslator.resultLiteral(x, prop);
  }
  
  /** {@inheritDoc} */
  @Override
  public final Object visitExprDeclPragma(final /*@non_null*/ ExprDeclPragma x, 
                                          final Object o) {
    
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
          t = Logic.Safe.and(t, prop.getInitiallyFOL());
          prop.setInitiallyFOL(t);
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
  
  /** {@inheritDoc} */
  @Override
  public final Object visitBinaryExpr(final /*@non_null*/ BinaryExpr expr, 
                                      final Object o) {
    final ContextProperties prop = (ContextProperties) o;
    Term res = null;
    switch(expr.op) {
      case TagConstants.EQ: 
        res = fTranslator.eq(expr, prop);
        break;
      case TagConstants.OR: 
        res = fTranslator.or(expr, prop);
        break;
      case TagConstants.AND: 
        res = fTranslator.and(expr, prop);
        break;
      case TagConstants.NE:
        res = fTranslator.ne(expr, prop);
        break;
      case TagConstants.GE: 
        res = fTranslator.ge(expr, prop);
        break;
      case TagConstants.GT: 
        res = fTranslator.gt(expr, prop);
        break;
      case TagConstants.LE: 
        res = fTranslator.le(expr, prop);
        break;
      case TagConstants.LT:  
        res = fTranslator.lt(expr, prop);
        break;
      case TagConstants.BITOR: 
        res = fTranslator.bitor(expr, prop);
        break;
      case TagConstants.BITXOR: 
        res = fTranslator.bitxor(expr, prop);
        break;
      case TagConstants.BITAND: 
        res = fTranslator.bitand(expr, prop);
        break;
      case TagConstants.LSHIFT:
        res = fTranslator.lshift(expr, prop);
        break;
      case TagConstants.RSHIFT: 
        res = fTranslator.rshift(expr, prop);
        break;
      case TagConstants.URSHIFT:
        res = fTranslator.urshift(expr, prop);
        break;
      case TagConstants.ADD: 
        res = fTranslator.add(expr, prop);
        break;
      case TagConstants.SUB: 
        res = fTranslator.sub(expr, prop);
        break;
      case TagConstants.DIV: 
        res = fTranslator.div(expr, prop);
        break;
      case TagConstants.MOD: 
        res = fTranslator.mod(expr, prop);
        break;
      case TagConstants.STAR: 
        res = fTranslator.star(expr, prop);
        break;
        
        
      case TagConstants.ASSIGN:
      case TagConstants.ASGMUL: 
      case TagConstants.ASGDIV: 
      case TagConstants.ASGREM: 
      case TagConstants.ASGADD: 
      case TagConstants.ASGSUB: 
      case TagConstants.ASGLSHIFT: 
      case TagConstants.ASGRSHIFT: 
      case TagConstants.ASGURSHIFT: 
      case TagConstants.ASGBITAND: 
        res = null; // no assignments in annotations
        break;
        
        // jml specific operators 
      case TagConstants.IMPLIES: 
        res = fTranslator.implies(expr, prop);
        break;
        
        // unsupported JML ops
      case TagConstants.EXPLIES:
      case TagConstants.IFF: // equivalence (equality)
      case TagConstants.NIFF:    // discrepance (xor)
      case TagConstants.SUBTYPE: 
      case TagConstants.DOTDOT: 
        res = null;
        break;
      default:
        throw new IllegalArgumentException("Unknown construct :" +
                                           TagConstants.toString(expr.op) +
                                           " " +  expr);
    }
    return res;

  }
  
  /** {@inheritDoc} */
  @Override
  public final Object visitVarExprModifierPragma(final /*@non_null*/ VarExprModifierPragma x, 
                                                 final Object o) {
    final MethodProperties prop = (MethodProperties) o;
    
    final RoutineDecl currentRoutine = prop.getDecl();
    final Post allExPosts = LookupJavaFe.getInst().getExceptionalPostcondition(currentRoutine);
    final QuantVariableRef commonExceptionVar = allExPosts.getRVar();

    final Term typeOfException = Type.translateToType(x.arg.type);
    final QuantVariableRef newExceptionVar = Expression.rvar(x.arg);

    Term newExPost = (Term)x.expr.accept(this, o);
    newExPost = newExPost.subst(newExceptionVar, commonExceptionVar);
    final Term guard = Logic.assignCompat(Heap.var, commonExceptionVar, typeOfException);
    final Post result = new Post (commonExceptionVar, Logic.Safe.implies(guard, newExPost));
    LookupJavaFe.getInst().addExceptionalPostcondition(prop.getDecl(), result);
    return null;
  }
  

  /** {@inheritDoc} */
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
        LookupJavaFe.getInst().addPrecondition(prop.getDecl(), t);
        break;
      case TagConstants.ENSURES:
      case TagConstants.POSTCONDITION:
      case TagConstants.POSTCONDITION_REDUNDANTLY:
        //addToPostcondition(t, o);
        LookupJavaFe.getInst().addNormalPostcondition(prop, t);
        break;
      default:
        break;
    }
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public final Object visitVarDeclStmt(final /*@non_null*/ VarDeclStmt x, final Object o) {
    //It's only called if we have a ghost variable declaration with maybe a set stmt
    
    final QuantVariableRef decl = Expression.rvar(x.decl); 
    Set.Assignment assign = null;
    if (x.decl.init != null) {
      assign = new Set.Assignment(Expression.rvar(x.decl),
                                               (Term) x.decl.init.accept(this, o));
    }
    return new Set(decl, assign);
  }
  
  /** {@inheritDoc} */
  @Override
  public /*@non_null*/ Object visitQuantifiedExpr(final /*@non_null*/ QuantifiedExpr x, 
                                                  final Object o) {
    return fTranslator.quantifier(x, (MethodProperties) o);
  }
  
  /** {@inheritDoc} */
  @Override
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
