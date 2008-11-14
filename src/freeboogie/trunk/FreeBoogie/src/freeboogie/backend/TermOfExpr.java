package freeboogie.backend;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Map;

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
 */
public class TermOfExpr extends Evaluator<Term> {
  // used only for its type
  private static final Term[] termArray = new Term[0];

  private TermBuilder term;
  private TcInterface tc;
  private SymbolTable st;
  private Map<Expr, Type> typeOf;

  public TermOfExpr() {}

  public void setBuilder(TermBuilder term) { this.term = term; }

  public void setTypeChecker(TcInterface tc) {
    this.tc = tc;
    this.st = tc.getST();
    this.typeOf = tc.getTypes();
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
    Type t;
    if (d instanceof VariableDecl) {
      t = ((VariableDecl)d).getType();
      if (TypeUtils.isInt(t)) return term.mk("var_int", id);
      if (TypeUtils.isBool(t)) return term.mk("var_bool", id);
      return term.mk("var", id);
    } else if (d instanceof ConstDecl) {
      // TODO I might want to keep track of constness
      t = ((ConstDecl)d).getType();
      if (TypeUtils.isInt(t)) return term.mk("var_int", id);
      if (TypeUtils.isBool(t)) return term.mk("var_bool", id);
      return term.mk("var", id);
    } else assert false; // what is it then?
    return null;
  }

  @Override
  public Term eval(AtomLit atomLit, AtomLit.AtomType val) {
    switch (val) {
    case TRUE:
      return term.mk("literal_formula", Boolean.valueOf(true));
    case FALSE:
      return term.mk("literal_formula", Boolean.valueOf(false));
    case NULL:
      return term.mk("literal_term", "null");
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
  public Term eval(AtomOld atomOld, Expr e) {
    assert false : "old() should have dissapeared during passivation";
    return e.eval(this);
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
    case PLUS: termId = "+"; break;
    case MINUS: termId = "-"; break;
    case MUL: termId = "*"; break;
    case DIV: termId = "/"; break;
    case MOD: termId = "%"; break;
    case EQ: 
      if (TypeUtils.isBool(lt)) termId = "iff";
      else if (TypeUtils.isInt(lt) && TypeUtils.isInt(rt)) termId = "eq_int";
      else termId = "eq";
      break;
    case NEQ:
      if (TypeUtils.isBool(lt)) termId = "xor";
      else if (TypeUtils.isInt(lt) && TypeUtils.isInt(rt)) termId = "neq_int";
      else termId = "neq";
      break;
    case LT: termId = "<"; break;
    case LE: termId = "<="; break;
    case GE: termId = ">="; break;
    case GT: termId = ">"; break;
    case SUBTYPE: termId = "<:"; break;
    case EQUIV: termId = "iff"; break;
    case IMPLIES: termId = "implies"; break;
    case AND: termId = "and"; break;
    case OR: termId = "or"; break;
    }
    return term.mk(termId, left.eval(this), right.eval(this));
  }

  @Override
  public Term eval(UnaryOp unaryOp, UnaryOp.Op op, Expr e) {
    String termId = "***unknown***";
    switch (op) {
    case MINUS: return term.mk("-", term.mk("literal_int", new BigInteger("0")), e.eval(this));
    case NOT: return term.mk("not", e.eval(this));
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
}
