package freeboogie.backend;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Map;

import freeboogie.ast.*;
import freeboogie.tc.*;
import freeboogie.util.Err;

/**
 * Builds {@code Term}s out of Boogie expressions.
 *
 * NOTE that some Boogie expressions should be dealt with
 * earlier, such as the old() built-in.
 *
 * TODO Make this (more) sorted. And test more.
 * TODO The stuff that is mentioned here should be registered by
 *      TermBuilder, not SmtTermBuilder.
 */
public class FormulaOfExpr extends Evaluator<Term> {
  // used only for its type
  private static final Term[] termArray = new Term[0];

  private TermOfExpr termOfExpr;

  private TermBuilder term;
  private TcInterface tc;
  private SymbolTable st;
  private Map<Expr, Type> typeOf;

  public FormulaOfExpr(TermOfExpr termOfExpr) {
    this.termOfExpr = termOfExpr;
  }

  public void setBuilder(TermBuilder term) {
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
  public Term eval(AtomCast atomCast, Expr e, Type type) {
    return e.eval(this);
  }

  @Override
  public Term eval(AtomFun atomFun, String function, TupleType types, Exprs args) {
    return formulaOfTerm(atomFun.eval(termOfExpr));
  }

  @Override
  public Term eval(AtomId atomId, String id, TupleType types) {
    // TODO check that atomId's boogie type is bool
    return term.mk("var_formula", id);
  }

  @Override
  public Term eval(AtomLit atomLit, AtomLit.AtomType val) {
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
  public Term eval(AtomMapSelect atomMapSelect, Atom atom, Exprs idx) {
    return formulaOfTerm(atomMapSelect.eval(termOfExpr));
  }

  @Override
  public Term eval(AtomQuant atomQuant, AtomQuant.QuantType quant, Declaration vars, Trigger trig, Expr e) {
    // TODO
    return term.mk("literal_formula", true);
  }

  @Override
  public Term eval(BinaryOp binaryOp, BinaryOp.Op op, Expr left, Expr right) {
    String termId = "***unknown***";
    Type lt = typeOf.get(left);
    Type rt = typeOf.get(right);
    switch (op) {
    case EQ: 
      if (TypeUtils.isBool(lt))
        return term.mk("iff", left.eval(this), right.eval(this));
      else if (TypeUtils.isInt(lt) && TypeUtils.isInt(rt)) 
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
      return term.mk("<:", left.eval(termOfExpr), right.eval(termOfExpr));
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
  public Term eval(UnaryOp unaryOp, UnaryOp.Op op, Expr e) {
    String termId = "***unknown***";
    switch (op) {
    case NOT: return term.mk("not", e.eval(this));
    default: 
      Err.internal("Attempting to make formula out of a unary op other than NOT.");
      return null;
    }
  }

  // === helpers ===
  private Term formulaOfTerm(Term t) {
    return term.mk("eq_bool", term.mk("literal_bool", "$$true"), t);
  }
}
