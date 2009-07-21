package freeboogie.backend;

import java.util.Map;

import genericutils.Err;

import freeboogie.ast.*;
import freeboogie.tc.*;

/**
 * Builds {@code Term}s out of Boogie expressions.
 *
 * NOTE that some Boogie expressions should be dealt with
 * earlier, such as the old() built-in.
 *
 * TODO Make this (more) sorted. And test more.
 * TODO The stuff that is mentioned here should be registered by
 *      TermBuilder, not SmtTermBuilder.
 *
 * @param <T> the type of terms
 */
public class FormulaOfExpr<T extends Term<T>> extends Evaluator<T> {
  private TermOfExpr<T> termOfExpr;
  private TermBuilder<T> term;

  private TcInterface tc;
  private SymbolTable st;
  private Map<Expr, Type> typeOf;

  public FormulaOfExpr(TermOfExpr<T> termOfExpr) {
    this.termOfExpr = termOfExpr;
  }

  public void setBuilder(TermBuilder<T> term) {
    this.term = term;
    termOfExpr.setBuilder(term);
  }

  public void setTypeChecker(TcInterface tc) {
    this.tc = tc;
    this.st = tc.getST();
    this.typeOf = tc.getTypes();
    termOfExpr.setTypeChecker(tc);
  }

  @Override
  public T eval(AtomCast atomCast, Expr e, Type type) {
    if (TypeUtils.isBool(type))
      return formulaOfTerm(atomCast.eval(termOfExpr));
    Err.internal(
      "Typechecking should have failed: non-bool in a bool's place.");
    return null;
  }

  @Override
  public T eval(AtomFun atomFun, String function, TupleType types, Exprs args) {
    return formulaOfTerm(atomFun.eval(termOfExpr));
  }

  @Override
  public T eval(AtomId atomId, String id, TupleType types) {
    // TODO check that atomId's boogie type is bool
    return term.mk("var_formula", id);
  }

  @Override
  public T eval(AtomLit atomLit, AtomLit.AtomType val) {
    switch (val) {
    case TRUE:
      return term.mk("literal_formula", Boolean.valueOf(true));
    case FALSE:
      return term.mk("literal_formula", Boolean.valueOf(false));
    default:
      Err.internal("Trying to make a formula out of a non-bool literal.");
      return null;
    }
  }

  @Override
  public T eval(AtomMapSelect atomMapSelect, Atom atom, Exprs idx) {
    return formulaOfTerm(atomMapSelect.eval(termOfExpr));
  }

  @Override
  public T eval(
    AtomQuant atomQuant,
    AtomQuant.QuantType quant,
    Declaration vars,
    Attribute attr,
    Expr e
  ) {
    T result = e.eval(this);
    while (vars != null) {
      VariableDecl vd = (VariableDecl) vars;      
      result = term.mk("forall", 
        term.mk("var", "term$$" + vd.getName()),
        result);
      vars = vd.getTail();
    }
    return result;
  }

  @Override
  public T eval(BinaryOp binaryOp, BinaryOp.Op op, Expr left, Expr right) {
    String termId = "***unknown***";
    Type lt = typeOf.get(left);
    Type rt = typeOf.get(right);
    switch (op) {
    case EQ: 
      // TODO figure out when EQ can be treated as EQUIV
      if (TypeUtils.isInt(lt) && TypeUtils.isInt(rt)) 
        return term.mk("eq_int", left.eval(termOfExpr), right.eval(termOfExpr));
      else 
        return term.mk("eq", left.eval(termOfExpr), right.eval(termOfExpr));
    case NEQ:
      if (TypeUtils.isBool(lt))
        return term.mk("not", term.mk("iff", left.eval(this), right.eval(this)));
      else if (TypeUtils.isInt(lt) && TypeUtils.isInt(rt))
        return term.mk("neq_int", left.eval(termOfExpr), right.eval(termOfExpr));
      else
        return term.mk("neq", left.eval(termOfExpr), right.eval(termOfExpr));
    case LT:
      return term.mk("<", left.eval(termOfExpr), right.eval(termOfExpr));
    case LE:
      return term.mk("<=", left.eval(termOfExpr), right.eval(termOfExpr));
    case GE:
      return term.mk(">=", left.eval(termOfExpr), right.eval(termOfExpr));
    case GT:
      return term.mk(">", left.eval(termOfExpr), right.eval(termOfExpr));
    case SUBTYPE:
      return formulaOfTerm(
        term.mk("<:", left.eval(termOfExpr), right.eval(termOfExpr)));
    case EQUIV:
      return term.mk("iff", left.eval(this), right.eval(this));
    case IMPLIES:
      return term.mk("implies", left.eval(this), right.eval(this));
    case AND: 
      return term.mk("and", left.eval(this), right.eval(this));
    case OR:
      return term.mk("or", left.eval(this), right.eval(this));
    default:
      Err.internal("Tried to make formula out of strange binary operator.");
      return null;
    }
  }

  @Override
  public T eval(UnaryOp unaryOp, UnaryOp.Op op, Expr e) {
    String termId = "***unknown***";
    switch (op) {
    case NOT: return term.mk("not", e.eval(this));
    default: 
      Err.internal("Attempting to make formula out of a unary op other than NOT.");
      return null;
    }
  }

  // === helpers ===
  private T formulaOfTerm(T t) {
    return term.mk("eq_bool", term.mk("literal_bool", Boolean.valueOf(true)), t);
  }
}
