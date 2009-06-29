package freeboogie.backend;

import java.math.BigInteger;
import java.util.*;

import genericutils.Err;

import freeboogie.ast.*;
import freeboogie.tc.*;

/**
 * Builds {@code Term}s out of Boogie expressions.
 *
 * NOTE that some Boogie expressions should be dealt with
 * earlier, such as the old() built-in.
 *
 * @param <T> the type of terms
 */
public class TermOfExpr<T extends Term<T>> extends Evaluator<T> {
  private TermBuilder<T> term;
  private TcInterface tc;
  private SymbolTable st;
  private Map<Expr, Type> typeOf;
  private Map<String, T> axioms = new HashMap<String, T>();

  public void setBuilder(TermBuilder<T> term) {
    this.term = term;
    axioms.put("literal_bool",
      term.mk("neq",
        term.mk("literal_bool", true),
        term.mk("literal_bool", false)));
    axioms.put("Tnand",
      term.mk("forall_bool", term.mk("var_bool", "a"),
      term.mk("forall_bool", term.mk("var_bool", "b"),
        term.mk("iff",
          term.mk("eq_bool",
            term.mk("Tnand",
              term.mk("var_bool", "a"),
              term.mk("var_bool", "b")),
            term.mk("literal_bool", true)),
          term.mk("not", term.mk("and",
            term.mk("eq_bool",
              term.mk("var_bool", "a"),
              term.mk("literal_bool", true)),
            term.mk("eq_bool",
              term.mk("var_bool", "b"),
              term.mk("literal_bool", true))))))));
    axioms.put("Tnand",
      term.mk("forall_bool", term.mk("var_bool", "a"),
      term.mk("forall_bool", term.mk("var_bool", "b"),
        term.mk("iff",
          term.mk("eq_bool",
            term.mk("Tnand",
              term.mk("var_bool", "a"),
              term.mk("var_bool", "b")),
            term.mk("literal_bool", false)),
          term.mk("and",
            term.mk("eq_bool",
              term.mk("var_bool", "a"),
              term.mk("literal_bool", true)),
            term.mk("eq_bool",
              term.mk("var_bool", "b"),
              term.mk("literal_bool", true)))))));
    axioms.put("T<",
      term.mk("forall_int", term.mk("var_int", "a"),
      term.mk("forall_int", term.mk("var_int", "b"),
        term.mk("iff",
          term.mk("eq_bool",
            term.mk("T<",
              term.mk("var_int", "a"),
              term.mk("var_int", "b")),
            term.mk("literal_bool", true)),
          term.mk("<",
            term.mk("var_int", "a"),
            term.mk("var_int", "b"))))));
    axioms.put("Teq",
      term.mk("forall", term.mk("var", "a"),
      term.mk("forall", term.mk("var", "b"),
        term.mk("iff",
          term.mk("eq_bool",
            term.mk("Teq", term.mk("var", "a"), term.mk("var", "b")),
            term.mk("literal_bool", true)),
          term.mk("eq", term.mk("var", "a"), term.mk("var", "b"))))));
    axioms.put("Teq_int",
      term.mk("forall_int", term.mk("var_int", "a"),
      term.mk("forall_int", term.mk("var_int", "b"),
        term.mk("iff",
          term.mk("eq_bool",
            term.mk("Teq_int",
              term.mk("var_int", "a"),
              term.mk("var_int", "b")),
            term.mk("literal_bool", true)),
          term.mk("eq_int",
            term.mk("var_int", "a"),
            term.mk("var_int", "b"))))));
    axioms.put("Teq_bool",
      term.mk("forall_bool", term.mk("var_bool", "a"),
      term.mk("forall_bool", term.mk("var_bool", "b"),
        term.mk("iff",
          term.mk("eq_bool",
            term.mk("Teq_bool",
              term.mk("var_bool", "a"),
              term.mk("var_bool", "b")),
            term.mk("literal_bool", true)),
          term.mk("iff",
            term.mk("eq_bool",
              term.mk("var_bool", "a"),
              term.mk("literal_bool", true)),
            term.mk("eq_bool",
              term.mk("var_bool", "b"),
              term.mk("literal_bool", true)))))));
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
    } else Err.internal("Unknown id declaration type for " + atomId + ": " + d);
    if (TypeUtils.isInt(t)) {
      // this prefix is needed for z3, but not simplify
      return mk("var_int", "term$$" + id);
    } else if (TypeUtils.isBool(t)) {
      // add axiom that connects terms to formulas
      T result = mk("var_bool", "term$$" + id);
      result.addAxiom(term.mk("iff",
        term.mk("var_formula", id),
        term.mk("eq_bool",
          term.mk("var_bool", "term$$" + id),
          term.mk("literal_bool", true))));
      return result;
    } else {
      // this prefix is needed for z3, but not simplify
      return mk("var", "term$$" + id);
    }
  }

  @Override
  public T eval(AtomLit atomLit, AtomLit.AtomType val) {
    switch (val) {
    case TRUE:
      return mk("literal_bool", true);
    case FALSE:
      return mk("literal_bool", false);
    case NULL:
      return mk("literal", "$$null");
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
  public T eval(
    AtomQuant atomQuant, 
    AtomQuant.QuantType quant, 
    Declaration vars, 
    Attribute attr, 
    Expr e
  ) {
    // TODO can this be done without HOL?
    Err.internal("Quantifiers are not supported in this position.");
    return null;
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
      return mk("+", l, r);
    case MINUS:
      return mk("-", l, r);
    case MUL:
      return mk("*", l, r);
    case DIV:
      return mk("/", l, r);
    case MOD:
      return mk("%", l, r);
    case EQ: 
      if (TypeUtils.isBool(lt))
        return mk("Teq_bool", l, r);
      else if (TypeUtils.isInt(lt) && TypeUtils.isInt(rt)) 
        return mk("Teq_int", l, r);
      else
        return mk("Teq", l, r);
    case NEQ:
      if (TypeUtils.isBool(lt))
        return not(mk("Teq_bool", l, r));
      else if (TypeUtils.isInt(lt) && TypeUtils.isInt(rt))
        return not(mk("Teq_int", l, r));
      else
        return not(mk("Teq", l, r));
    case LT:
      return mk("T<", l, r);
    case LE:
      return or(mk("T<", l, r), mk("Teq_int", l, r));
    case GE:
      return or(mk("T<", r, l), mk("Teq_int", r, l));
    case GT:
      return mk("T<", l, r);
    case SUBTYPE:
      return mk("<:", l, r);
    case EQUIV:
      return mk("Tnand", mk("Tnand", l, r), or(l, r));
    case IMPLIES:
      return mk("Tnand", l, not(r));
    case AND:
      return not(mk("Tnand", l, r));
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
    case MINUS: return mk("-", mk("literal_int", new BigInteger("0")), e.eval(this));
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
    return mk("Tnand", t, t);
  }

  private T or(T x, T y) {
    return mk("Tnand", not(x), not(y));
  }

  private T decorate(String id, T t) {
    T a = axioms.get(id);
    if (a != null) t.addAxiom(a);
    return t;
  }

  private T mk(String id, Object a) {
    return decorate(id, term.mk(id, a));
  }

  private T mk(String id, T a) {
    return decorate(id, term.mk(id, a));
  }

  private T mk(String id, T a, T b) {
    return decorate(id, term.mk(id, a, b));
  }

  private T mk(String id, ArrayList<T> a) {
    return decorate(id, term.mk(id, a));
  }
}
