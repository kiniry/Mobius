package mobius.directvcgen.translator;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import javafe.ast.BinaryExpr;
import javafe.ast.FieldAccess;
import javafe.ast.GenericVarDecl;
import javafe.ast.InstanceOfExpr;
import javafe.ast.LiteralExpr;
import javafe.ast.ThisExpr;
import javafe.ast.VariableAccess;
import mobius.directvcgen.formula.Bool;
import mobius.directvcgen.formula.Expression;
import mobius.directvcgen.formula.Heap;
import mobius.directvcgen.formula.Logic;
import mobius.directvcgen.formula.Num;
import mobius.directvcgen.formula.Ref;
import mobius.directvcgen.formula.Type;
import mobius.directvcgen.translator.struct.ContextProperties;
import mobius.directvcgen.translator.struct.MethodProperties;
import escjava.ast.NaryExpr;
import escjava.ast.QuantifiedExpr;
import escjava.ast.ResExpr;
import escjava.ast.TagConstants;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;

class JmlExprToFormula {

  private final JmlVisitor fVisitor;

  public JmlExprToFormula(final JmlVisitor visitor) {
    fVisitor = visitor;
  }

  public Term and(final BinaryExpr expr, final ContextProperties prop) {
    final Term t1 = (Term)expr.left.accept(fVisitor, prop);
    final Term t2 = (Term)expr.right.accept(fVisitor, prop);

    if (!prop.isInspectingPred() && 
        (t1.getSort() != Logic.sort) &&
        (t2.getSort() != Logic.sort)) {
      return Bool.and(t1, t2);
    }
    else {
      return Logic.and(Logic.boolToPred(t1), Logic.boolToPred(t2));
    }
  }


  public Term or(final BinaryExpr expr, final ContextProperties prop) {
    final Term t1 = (Term)expr.left.accept(fVisitor, prop);
    final Term t2 = (Term)expr.right.accept(fVisitor, prop);

    if (!prop.isInspectingPred() && 
        (t1.getSort() != Logic.sort) && 
        (t2.getSort() != Logic.sort)) {
      return Bool.or(t1, t2);
    }
    else {
      return Logic.or(Logic.boolToPred(t1), Logic.boolToPred(t2));
    }
  }


  public Term add(final BinaryExpr expr, final ContextProperties o) {
    final Term t1 = (Term)expr.left.accept(fVisitor, o);
    final Term t2 = (Term)expr.right.accept(fVisitor, o);

    return Num.add(t1, t2);
  }

  /**
   * Returns either a sortPred or sortBool equality term depending of the 
   * expection of the upper method.
   * @param expr binary expression with a left and a right expression
   * @param prop the Properties object, contains information about the excepted 
   * sort of the return value
   * @return term in the excepted sort, if possible
   */
  public Term eq(final BinaryExpr expr, final ContextProperties prop) {
    final boolean predOld = prop.isInspectingPred();
    //set Properties.prop:=false (equality operation wants sortBool)
    prop.setInspectingPred(false);
    final Term t1 = (Term)expr.left.accept(fVisitor, prop);
    final Term t2 = (Term)expr.right.accept(fVisitor, prop);
    prop.setInspectingPred(predOld);
    if (!predOld && 
        (t1.getSort() != Logic.sort) &&
        (t2.getSort() != Logic.sort)) {
      return Bool.equals(t1, t2);
    }
    else if (predOld && 
        (t1.getSort() != Logic.sort) && 
        (t2.getSort() != Logic.sort)) {
      return Logic.equals(t1, t2);
    }
    else {
      return Logic.fullImplies(Logic.boolToPred(t1), Logic.boolToPred(t2));
    }
  }


  /**
   * ne(t1,t2) <--> not(equal(t1,t2)).
   */
  public Term ne(final BinaryExpr expr, final ContextProperties prop) {
    final Term t = eq(expr, prop);

    if (!prop.isInspectingPred() && (t.getSort() != Logic.sort)) {
      return Bool.not(t);
    }
    else {
      return Logic.not(Logic.boolToPred(t));
    }
  }



  public Term ge(final BinaryExpr expr, final ContextProperties prop) {
        
    final Term t1 = (Term)expr.left.accept(fVisitor, prop);
    final Term t2 = (Term)expr.right.accept(fVisitor, prop);

    if (!prop.isInspectingPred()) {
      return Bool.ge(t1, t2);
    }
    else {
      return Logic.ge(t1, t2);
    }
  }


  public Term gt(final BinaryExpr expr, final ContextProperties prop) {
    final Term t1 = (Term)expr.left.accept(fVisitor, prop);
    final Term t2 = (Term)expr.right.accept(fVisitor, prop);

    if (!prop.isInspectingPred()) {
      return Bool.gt(t1, t2);
    }
    else {
      return Logic.gt(t1, t2);
    }
  }


  public Term le(final BinaryExpr expr, final ContextProperties prop) {
    final Term t1 = (Term)expr.left.accept(fVisitor, prop);
    final Term t2 = (Term)expr.right.accept(fVisitor, prop);

    if (!prop.isInspectingPred()) {
      return Bool.le(t1, t2);
    }
    else {
      return Logic.le(t1, t2);
    }
  }


  public Term lt(final BinaryExpr expr, final ContextProperties prop) {
    final Term t1 = (Term)expr.left.accept(fVisitor, prop);
    final Term t2 = (Term)expr.right.accept(fVisitor, prop);

    if (!prop.isInspectingPred()) {
      return Bool.lt(t1, t2);
    }
    else {
      return Logic.lt(t1, t2);
    }
  }

  public Term bitor(final BinaryExpr expr, final ContextProperties o) {
    final Term t1 = (Term)expr.left.accept(fVisitor, o);
    final Term t2 = (Term)expr.right.accept(fVisitor, o);
    return Expression.bitor(t1, t2);
  }

  public Term bitxor(final BinaryExpr expr, final ContextProperties o) {
    final Term t1 = (Term)expr.left.accept(fVisitor, o);
    final Term t2 = (Term)expr.right.accept(fVisitor, o);
    return Expression.bitxor(t1, t2);
  }

  public Term bitand(final BinaryExpr expr, final ContextProperties o) {
    final Term t1 = (Term)expr.left.accept(fVisitor, o);
    final Term t2 = (Term)expr.right.accept(fVisitor, o);
    return Expression.bitand(t1, t2);
  }

  public Term lshift(final BinaryExpr expr, final ContextProperties o) {
    final Term t1 = (Term)expr.left.accept(fVisitor, o);
    final Term t2 = (Term)expr.right.accept(fVisitor, o);
    return Num.lshift(t1, t2);
  }

  public Term rshift(final BinaryExpr expr, final ContextProperties o) {
    final Term t1 = (Term)expr.left.accept(fVisitor, o);
    final Term t2 = (Term)expr.right.accept(fVisitor, o);
    return Num.rshift(t1, t2);
  }

  public Term urshift(final BinaryExpr expr, final ContextProperties o) {
    final Term t1 = (Term)expr.left.accept(fVisitor, o);
    final Term t2 = (Term)expr.right.accept(fVisitor, o);
    return Num.urshift(t1, t2);
  }

  public Term sub(final BinaryExpr expr, final ContextProperties o) {
    final Term t1 = (Term)expr.left.accept(fVisitor, o);
    final Term t2 = (Term)expr.right.accept(fVisitor, o);
    return Num.sub(t1, t2);
  }

  public Term div(final BinaryExpr expr, final ContextProperties o) {
    final Term t1 = (Term)expr.left.accept(fVisitor, o);
    final Term t2 = (Term)expr.right.accept(fVisitor, o);
    return Num.div(t1, t2);
  }

  public Term mod(final BinaryExpr expr, final ContextProperties o) {
    final Term t1 = (Term)expr.left.accept(fVisitor, o);
    final Term t2 = (Term)expr.right.accept(fVisitor, o);
    return Num.mod(t1, t2);
  }

  public Term star(final BinaryExpr expr, final ContextProperties o) {
    final Term t1 = (Term)expr.left.accept(fVisitor, o);
    final Term t2 = (Term)expr.right.accept(fVisitor, o);
    return Num.mul(t1, t2);
  }


  public Term implies(final BinaryExpr expr, final ContextProperties o) {
    final Term t1 = (Term)expr.left.accept(fVisitor, o);
    final Term t2 = (Term)expr.right.accept(fVisitor, o);

    if (!o.isInspectingPred() && 
        (t1.getSort() != Logic.sort) &&
        (t2.getSort() != Logic.sort)) {
      return Bool.implies(t1, t2);
    }
    else {
      return Logic.implies(Logic.boolToPred(t1), Logic.boolToPred(t2));
    }
  }


  public Term instanceOfExpr(final InstanceOfExpr x, final ContextProperties o) {
    final Term refTerm = (Term) x.expr.accept(this.fVisitor, o);

    final Term sortType = Type.translateToType(x.type);
    return Logic.assignCompat(Heap.var, refTerm, sortType);
  }



  
  public Term literal(final LiteralExpr x, final ContextProperties o) {

    switch (x.getTag()) {
      case TagConstants.BOOLEANLIT: 
        return Bool.value((Boolean) x.value);
      case TagConstants.INTLIT:
        return Num.value((Integer) x.value);
      case TagConstants.LONGLIT:
        return Num.value((Long) x.value);
      case TagConstants.CHARLIT:
        return Num.value((Character) x.value);
      case TagConstants.FLOATLIT:
        return Num.value((Float) x.value);
      case TagConstants.DOUBLELIT:
        return Num.value((Double) x.value);

      case TagConstants.STRINGLIT:
        return null;
      
      case TagConstants.NULLLIT:
        return Ref.nullValue();
      
      case TagConstants.BYTELIT:
        return Num.value((Byte) x.value);
      
      case TagConstants.SHORTLIT:
        return Num.value((Short) x.value);
      default: 
        throw new IllegalArgumentException("LiteralExpr " + x.toString() + 
                                           " has unknown type.");  
                                              // should be unreachable
    }
  }

  
  public QuantVariableRef resultLiteral(final ResExpr x, 
                                        final MethodProperties prop) {
    final QuantVariableRef qvr = prop.fResult;
    if (qvr == null) {
      throw new NullPointerException();
      // should not be called if the method returns void
    }
    return qvr;
  }

  public Term variableAccess(final VariableAccess x, final ContextProperties prop) {
    Term res = null;
    
    if (prop.isOld()) { 
      res = Expression.old(x.decl); // x.decl cannot be null
    }
    else {
      res = Expression.rvar(x.decl);
    }
    
    if (prop.isInspectingPred() && (res.getSort() == Bool.sort)) {
      res = Logic.boolToPred(res);
    }
    return res;
  }

  public Term genericVarDecl(final GenericVarDecl x, final ContextProperties prop) {
    Term res;
    if (prop.isOld()) {
      res = Expression.old(x);
    }
    else { 
      res = Expression.rvar(x);
    }
    if (prop.isInspectingPred() && (res.getSort() == Bool.sort)) {
      res = Logic.boolToPred(res);
    }
    return res;
  }

  public Term fieldAccess(final FieldAccess fieldAccess, final ContextProperties prop) {
    if (prop.isFresh()) { 
      final QuantVariableRef qref = Expression.rvar(fieldAccess.decl);
      final Set<QuantVariableRef> freshSet = prop.getFreshVariables();
      freshSet.add(qref);
    }
    else { 
      if (fVisitor.getDoSubsetChecking()) {
        fVisitor.fGlobal.addSubsetCheckingSet(fieldAccess);
      }
      final boolean oldProp = prop.isOld();
      final Term obj = (Term) fieldAccess.od.accept(fVisitor, prop);
      QuantVariable var = null;
      QuantVariableRef heap = Heap.var;
      if (oldProp) {
        heap = Heap.varPre;
      }
      var = Expression.var(fieldAccess.decl);
      final Sort type = Type.getSort(fieldAccess);
      return Heap.select(heap, obj, var, type);
    }
    return null;
  }
  
  
  /**
   * Builds up a FOL term as: \fresh(x,y) --> and(%fresh(x:ref),%(y:ref)):PRED.
   * @param x the NaryExpr with TagConstant.FRESH
   * @param prop properties object holding whether fresh property is set and holds the freshSet
   * @return the generated FOL term
   */
  public Term freshExpr(final NaryExpr x, final ContextProperties prop) { 
    prop.setFresh(true);
    fVisitor.visitGCExpr(x, prop);
    prop.setFresh(false);
    final Set<QuantVariableRef> freshVars = prop.getFreshVariables();
    
    Term res = null;
    for (QuantVariableRef qvr: freshVars) {
      if (res == null) {
        res = doFreshTerm(qvr);
      }
      else { 
        res = Logic.and(res, doFreshTerm(qvr));
      }
    }
    
    return res;
  }

  
  
  
  /**
   * Generates a Term of an fresh variable: (x != null) and 
   * !isAlive(Pre_Heap, x) and isAlive(Heap, x).
   * @param qref the Term to translate into a fresh FOL term
   * @return the generated FOL term
   */
  public Term doFreshTerm(final QuantVariableRef qref) {
    final Term notEqualNull = Logic.not(Logic.equalsNull(qref));
    final Term isNotAliveInPreHeap = Logic.not(Logic.isAlive(Heap.varPre, qref));
    final Term isAliveInHeap = Logic.isAlive(Heap.var, qref);
    return Logic.and(Logic.and(notEqualNull, isNotAliveInPreHeap), isAliveInHeap);
  }
  
  public Term oldExpr(final NaryExpr x, final ContextProperties prop) {
    final boolean old = prop.isOld();
    prop.setOld(true);
    final Term res = (Term) fVisitor.visitGCExpr(x, prop);
    prop.setOld(old);
    return res;
  }

  public Term thisLiteral(final ThisExpr x, final ContextProperties o) {
    return Ref.varThis;
  }

  
  public Term quantifier(final QuantifiedExpr x, final MethodProperties prop) {
    prop.setQuantifier(true);
    fVisitor.visitGCExpr(x, prop);  
    prop.setQuantifier(false);
    
    final List<QuantVariable> qVarsSet = new ArrayList<QuantVariable>(); 
    qVarsSet.addAll(prop.getQuantVars());

    prop.clearQuantVars();
    final Term exprTerm = (Term) x.expr.accept(fVisitor, prop);
    final QuantVariable[] qVarsArray = qVarsSet.toArray(new QuantVariable[qVarsSet.size()]);
    
    if (x.quantifier == TagConstants.FORALL) {
      return Logic.forall(qVarsArray, exprTerm);
    }
    else {
      return Logic.exists(qVarsArray, exprTerm);
    }
  }

}
 
