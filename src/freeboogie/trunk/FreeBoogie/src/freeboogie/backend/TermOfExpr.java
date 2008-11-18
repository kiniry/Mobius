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
public class TermOfExpr extends Evaluator<Term> {
  // used only for its type
  private static final Term[] termArray = new Term[0];

  private TermBuilder term;
  private TcInterface tc;
  private SymbolTable st;
  private Map<Expr, Type> typeOf;

  private HashSet<String> boolsAsTerm;
  private boolean trueFalseAxiom;

  public TermOfExpr() {
    boolsAsTerm = new HashSet<String>(103);
  }

  public void setBuilder(TermBuilder term) { this.term = term; }

  public void setTypeChecker(TcInterface tc) {
    this.tc = tc;
    this.st = tc.getST();
    this.typeOf = tc.getTypes();
  }

  public List<Term> getAssumptions() {
    List<Term> result = new ArrayList<Term>(2 * boolsAsTerm.size());
    for (String id : boolsAsTerm) {
      result.add(term.mk("iff",
        term.mk("var_formula", id),
        term.mk("eq_bool",
          term.mk("var_bool", "term$$" + id),
          term.mk("literal_bool", "$$true"))));
    }
    return result;
  }

  @Override
  public Term eval(AtomCast atomCast, Expr e, Type type) {
    return e.eval(this);
  }

  @Override
  public Term eval(AtomFun atomFun, String function, TupleType types, Exprs args) {
    return term.mk(function, tuple(args));
  }

  @Override
  public Term eval(AtomId atomId, String id, TupleType types) {
    Declaration d = st.ids.def(atomId);
    Type t = null;
    if (d instanceof VariableDecl) {
      t = ((VariableDecl)d).getType();
    } else if (d instanceof ConstDecl) {
      // TODO I might want to keep track of constness
      t = ((ConstDecl)d).getType();
    } else Err.internal("Unkknown id declaration type for " + id + ".");
    if (TypeUtils.isInt(t)) {
      return term.mk("var_int", id);
    } else if (TypeUtils.isBool(t)) {
      boolsAsTerm.add(id);
      return term.mk("var_bool", "term$$" + id);
    } else {
      return term.mk("var", id);
    }
  }

  @Override
  public Term eval(AtomLit atomLit, AtomLit.AtomType val) {
    switch (val) {
    case TRUE:
      trueFalseAxiom = true;
      return term.mk("literal_bool", "$$true");
    case FALSE:
      trueFalseAxiom = true;
      return term.mk("literal_bool", "$$false");
    case NULL:
      return term.mk("literal", "$$null");
    default:
      assert false;
      return null;
    }
  }

  @Override
  public Term eval(AtomMapSelect atomMapSelect, Atom atom, Exprs idx) {
    Type t = typeOf.get(atomMapSelect);
    String termId = "map_select";
    if (TypeUtils.isInt(t)) termId = "map_select_int";
    if (TypeUtils.isBool(t)) termId = "map_select_bool";
    return term.mk(termId, atom.eval(this), term.mk("tuple", tuple(idx)));
  }

  @Override
  public Term eval(AtomMapUpdate atomMapUpdate, Atom atom, Exprs idx, Expr val) {
    return term.mk(
      "map_update", 
      new Term[] {
        atom.eval(this), 
        term.mk("tuple", tuple(idx)),
        val.eval(this)});
  }

  @Override
  public Term eval(AtomNum atomNum, BigInteger val) {
    return term.mk("literal_int", val);
  }

  @Override
  public Term eval(AtomQuant atomQuant, AtomQuant.QuantType quant, Declaration vars, Trigger trig, Expr e) {
    // TODO implement; use term$$forall; 
    //   also, introduce one axiom per quantified var
    return term.mk("literal_bool", Boolean.valueOf(true));
  }

  @Override
  public Term eval(BinaryOp binaryOp, BinaryOp.Op op, Expr left, Expr right) {
    String termId = "***unknown***";
    Type lt = typeOf.get(left);
    Type rt = typeOf.get(right);
    Term l = left.eval(this);
    Term r = right.eval(this);
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
  public Term eval(UnaryOp unaryOp, UnaryOp.Op op, Expr e) {
    String termId = "***unknown***";
    switch (op) {
    case MINUS: return term.mk("-", term.mk("literal_int", new BigInteger("0")), e.eval(this));
    case NOT: return not(e.eval(this));
    default: assert false; return null;
    }
  }

  // === helpers ===
  private Term[] tuple(Exprs e) {
    ArrayList<Term> r = new ArrayList<Term>(23);
    while (e != null) {
      r.add(e.getExpr().eval(this));
      e = e.getTail();
    }
    return r.toArray(termArray);
  }

  private Term not(Term t) {
    return term.mk("Tnand", t, t);
  }

  private Term or(Term x, Term y) {
    return term.mk("Tnand", not(x), not(y));
  }
}
