package freeboogie.backend;

import java.math.BigInteger;
import java.util.*;

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
public class TermOfExpr<T extends Term<T>> extends Evaluator<T> {
  private T TRUE_TERM;
  private T FALSE_TERM;
  private T TRUE_NEQ_FALSE;

  private TermBuilder<T> term;
  private TcInterface tc;
  private SymbolTable st;
  private Map<Expr, Type> typeOf;

  public void setBuilder(TermBuilder<T> term) {
    this.term = term;
    TRUE_TERM = term.mk("literal_bool", Boolean.valueOf(true));
    FALSE_TERM = term.mk("literal_bool", Boolean.valueOf(false));
    TRUE_NEQ_FALSE = term.mk("neq", TRUE_TERM, FALSE_TERM);
    TRUE_TERM.addAxiom(TRUE_NEQ_FALSE);
    FALSE_TERM.addAxiom(TRUE_NEQ_FALSE);
  }

  public void setTypeChecker(TcInterface tc) {
    this.tc = tc;
    this.st = tc.getST();
    this.typeOf = tc.getTypes();
  }

  @Override
  public T eval(AtomCast atomCast, Expr e, Type type) {
    T result = e.eval(this);
    if (TypeUtils.isInt(type))
      return term.mk("cast_to_int", result);
    if (TypeUtils.isBool(type))
      return term.mk("cast_to_bool", result);
    return result;
  }

  @Override
  public T eval(AtomFun atomFun, String function, TupleType types, Exprs args) {
    String prefix = "funT_";
    if (TypeUtils.isInt(typeOf.get(atomFun)))
      prefix = "funI_";
    if (TypeUtils.isBool(typeOf.get(atomFun)))
      prefix = "funB_";
    return term.mk(prefix + function, tuple(args));
  }

  @Override
  public T eval(AtomId atomId, String id, TupleType types) {
    Declaration d = st.ids.def(atomId);
    Type t = null;
    if (d instanceof VariableDecl) {
      t = ((VariableDecl)d).getType();
    } else if (d instanceof ConstDecl) {
      // TODO I might want to keep track of constness
      t = ((ConstDecl)d).getType();
    } else Err.internal("Unknown id declaration type for " + id + ".");
    if (TypeUtils.isInt(t)) {
      // this prefix is needed for z3, but not simplify
      return term.mk("var_int", "term$$" + id);
    } else if (TypeUtils.isBool(t)) {
      return booleanVarTerm(id);
    } else {
      // this prefix is needed for z3, but not simplify
      return term.mk("var", "term$$" + id);
    }
  }

  @Override
  public T eval(AtomLit atomLit, AtomLit.AtomType val) {
    switch (val) {
    case TRUE:
      return TRUE_TERM;
    case FALSE:
      return FALSE_TERM;
    case NULL:
      return term.mk("literal", "$$null");
    default:
      assert false;
      return null;
    }
  }

  @Override
  public T eval(AtomMapSelect atomMapSelect, Atom atom, Exprs idx) {
    Type t = typeOf.get(atomMapSelect);
    String termId = "map_select";
    if (TypeUtils.isInt(t)) termId = "map_select_int";
    if (TypeUtils.isBool(t)) termId = "map_select_bool";
    return term.mk(termId, atom.eval(this), term.mk("tuple", tuple(idx)));
  }

  @Override
  public T eval(AtomMapUpdate atomMapUpdate, Atom atom, Exprs idx, Expr val) {
    return term.mk(
      "map_update", 
      new Term[] {
        atom.eval(this), 
        term.mk("tuple", tuple(idx)),
        val.eval(this)});
  }

  @Override
  public T eval(AtomNum atomNum, BigInteger val) {
    return term.mk("literal_int", val);
  }

  @Override
  public T eval(AtomQuant atomQuant, AtomQuant.QuantType quant, Declaration vars, Trigger trig, Expr e) {
    // TODO implement; use term$$forall; 
    //   also, introduce one axiom per quantified var
    return term.mk("literal_bool", Boolean.valueOf(true));
  }

  @Override
  public T eval(BinaryOp binaryOp, BinaryOp.Op op, Expr left, Expr right) {
    String termId = "***unknown***";
    Type lt = typeOf.get(left);
    Type rt = typeOf.get(right);
    T l = left.eval(this);
    T r = right.eval(this);
    switch (op) {
    case PLUS:
      return term.mk("+", l, r);
    case MINUS:
      return term.mk("-", l, r);
    case MUL:
      return term.mk("*", l, r);
    case DIV:
      return term.mk("/", l, r);
    case MOD:
      return term.mk("%", l, r);
    case EQ: 
      if (TypeUtils.isBool(lt))
        return term.mk("Teq_bool", l, r);
      else if (TypeUtils.isInt(lt) && TypeUtils.isInt(rt)) 
        return term.mk("Teq_int", l, r);
      else
        return term.mk("Teq", l, r);
    case NEQ:
      if (TypeUtils.isBool(lt))
        return not(term.mk("Teq_bool", l, r));
      else if (TypeUtils.isInt(lt) && TypeUtils.isInt(rt))
        return not(term.mk("Teq_int", l, r));
      else
        return not(term.mk("Teq", l, r));
    case LT:
      return term.mk("T<", l, r);
    case LE:
      return or(term.mk("T<", l, r), term.mk("Teq_int", l, r));
    case GE:
      return or(term.mk("T<", r, l), term.mk("Teq_int", r, l));
    case GT:
      return term.mk("T<", l, r);
    case SUBTYPE:
      return term.mk("<:", l, r);
    case EQUIV:
      return term.mk("Tnand", term.mk("Tnand", l, r), or(l, r));
    case IMPLIES:
      return term.mk("Tnand", l, not(r));
    case AND:
      return not(term.mk("Tnand", l, r));
    case OR:
      return or(l, r);
    default:
      Err.internal("Unknown binary operator.");
      return null;
    }
  }

  @Override
  public T eval(UnaryOp unaryOp, UnaryOp.Op op, Expr e) {
    String termId = "***unknown***";
    switch (op) {
    case MINUS: return term.mk("-", term.mk("literal_int", new BigInteger("0")), e.eval(this));
    case NOT: return not(e.eval(this));
    default: assert false; return null;
    }
  }

  // === helpers ===
  private ArrayList<T> tuple(Exprs e) {
    ArrayList<T> r = new ArrayList<T>(23);
    while (e != null) {
      r.add(e.getExpr().eval(this));
      e = e.getTail();
    }
    return r;
  }

  private T not(T t) {
    return term.mk("Tnand", t, t);
  }

  private T or(T x, T y) {
    return term.mk("Tnand", not(x), not(y));
  }

  private T booleanVarTerm(String id) {
    T result = term.mk("var_bool", "term$$" + id);
    T axiom = term.mk("iff",
        term.mk("var_formula", id),
        term.mk("eq_bool",
          term.mk("var_bool", "term$$" + id),
          term.mk("literal_bool", Boolean.valueOf(true))));
    result.addAxiom(axiom);
    return result;
  }
}
