package mobius.logic.lang.boogie;

//{{{ imports
import java.math.BigInteger;
import java.util.LinkedList;

import freeboogie.ast.Atom;
import freeboogie.ast.AtomCast;
import freeboogie.ast.AtomFun;
import freeboogie.ast.AtomId;
import freeboogie.ast.AtomLit;
import freeboogie.ast.AtomMapSelect;
import freeboogie.ast.AtomNum;
import freeboogie.ast.AtomQuant;
import freeboogie.ast.Axiom;
import freeboogie.ast.BinaryOp;
import freeboogie.ast.ConstDecl;
import freeboogie.ast.Declaration;
import freeboogie.ast.DepType;
import freeboogie.ast.Evaluator;
import freeboogie.ast.Expr;
import freeboogie.ast.Exprs;
import freeboogie.ast.Function;
import freeboogie.ast.Identifiers;
import freeboogie.ast.IndexedType;
import freeboogie.ast.MapType;
import freeboogie.ast.PrimitiveType;
import freeboogie.ast.Procedure;
import freeboogie.ast.Signature;
import freeboogie.ast.Specification;
import freeboogie.ast.Trigger;
import freeboogie.ast.TupleType;
import freeboogie.ast.Type;
import freeboogie.ast.TypeDecl;
import freeboogie.ast.UnaryOp;
import freeboogie.ast.UserType;
import freeboogie.ast.VariableDecl;
import mobius.logic.lang.generic.ast.Clause;
import mobius.logic.lang.generic.ast.ClauseList;
import mobius.logic.lang.generic.ast.GenericAst;
//}}}


/**
 * Transforms Boogie into FOL. 
 * @author rgrig@
 */
public class GenericOfBoogie extends Evaluator<GenericAst> {
  /** 
   * If I could make checkstyle shut-up about the "complexity"
   * of simpler alternatives to this mess, I would use them. In
   * particular, notice how removing the "Wtf" comment makes
   * checkstyle terribly unhappy.
   */
  private static enum IdOfOp { /** Wtf? */
    /** Plus. */ PLUS(BinaryOp.Op.PLUS, "+"),
    /** Minus. */ MINUS(BinaryOp.Op.MINUS, "-"),
    /** Mul. */ MUL(BinaryOp.Op.MUL, "*"),
    /** Div. */ DIV(BinaryOp.Op.DIV, "/"),
    /** Mod. */ MOD(BinaryOp.Op.MOD, "%"),
    /** Eq. */ EQ(BinaryOp.Op.EQ, "="),
    /** Neq. */ NEQ(BinaryOp.Op.NEQ, "!="),
    /** Lt. */ LT(BinaryOp.Op.LT, "<"),
    /** Le. */ LE(BinaryOp.Op.LE, "<="),
    /** Ge. */ GE(BinaryOp.Op.GE, ">="),
    /** Gt. */ GT(BinaryOp.Op.GT, ">"),
    /** Subtype. */ SUBTYPE(BinaryOp.Op.SUBTYPE, "<:"),
    /** Equiv. */ EQUIV(BinaryOp.Op.EQUIV, "<->"),
    /** Implies. */ IMPLIES(BinaryOp.Op.IMPLIES, "->"),
    /** And. */ AND(BinaryOp.Op.AND, "and"),
    /** Or. */ OR(BinaryOp.Op.OR, "or");

    /** Operator. */
    private final BinaryOp.Op fOp;

    /** String representation. */
    private final String fVal;

    /** 
     * Construct an association from Boogie operators to their String rep. 
     * @param op the binary operator
     * @param val the string representation
     */
    IdOfOp(final BinaryOp.Op op, final String val) {
      fOp = op;
      fVal = val;
    }

    /**
     * @param op a boogie operator 
     * @return the FOL representation
     */
    public static String get(final BinaryOp.Op op) {
      for (IdOfOp v : values()) {
        if (op == v.fOp) { return v.fVal; }
      }
      return null;
    }
  }

  /** The result. This idiotic comment is forced by checkstyle. */
  private LinkedList<GenericAst> fResult;

  public ClauseList getFrom(final Declaration boogie) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(
    final AtomCast atomCast, 
    final Expr e, 
    final Type type
  ) {
    return e.eval(this);
  }

  /** {@inheritDoc} */
  @Override
  public mobius.logic.lang.generic.ast.Application eval(
    final AtomFun atomFun, 
    final String function, 
    final TupleType types, 
    final Exprs args
  ) {
    return mobius.logic.lang.generic.ast.Application.mk(
      args == null? null : (mobius.logic.lang.generic.ast.Term)args.eval(this),
      mobius.logic.lang.generic.ast.Atom.mk(null, function));
  }

  /** {@inheritDoc} */
  @Override
  public mobius.logic.lang.generic.ast.Atom eval(
    final AtomId atomId, 
    final String id, 
    final TupleType types
  ) {
    return mobius.logic.lang.generic.ast.Atom.mk(null, id);
  }

  /** {@inheritDoc} */
  @Override
  public mobius.logic.lang.generic.ast.Atom eval(
    final AtomLit atomLit, 
    final AtomLit.AtomType val
  ) {
    String id;
    switch (val) {
      case TRUE: 
        id = "true"; break;
      case FALSE: 
        id = "false"; break;
      default: 
        id = null;
        assert false : "Huh?";
    }
    return mobius.logic.lang.generic.ast.Atom.mk(null, id);
  }

  /** {@inheritDoc} */
  @Override
  public mobius.logic.lang.generic.ast.Application eval(
    final AtomMapSelect atomMapSelect, 
    final Atom atom, 
    final Exprs idx
  ) {
    return mobius.logic.lang.generic.ast.Application.mk(
      (mobius.logic.lang.generic.ast.Term)atom.eval(this),
      idx == null? null : (mobius.logic.lang.generic.ast.Term)idx.eval(this));
  }

  /** {@inheritDoc} */
  @Override
  public mobius.logic.lang.generic.ast.Atom eval(
    final AtomNum atomNum, 
    final BigInteger val
  ) {
    return mobius.logic.lang.generic.ast.Atom.mk(null, val.toString());
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(
    final AtomQuant atomQuant, 
    final AtomQuant.QuantType quant, 
    final Declaration vars, 
    final Trigger trig, 
    final Expr e
  ) {
    switch (quant) {
      case FORALL:
        return mobius.logic.lang.generic.ast.Forall.mk(
          null, 
          vars == null? 
            null : 
            (mobius.logic.lang.generic.ast.Atom)vars.eval(this),
          (mobius.logic.lang.generic.ast.Term)e.eval(this));
      case EXISTS:
        assert false : "not implemented";
        break;
      default:
        assert false : "Huh?";
    }
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(
    final Axiom axiom,
    final String name, 
    final Identifiers typeVars, 
    final Expr expr, 
    final Declaration tail
  ) {
    fResult.add(Clause.mk(
      name,
      (mobius.logic.lang.generic.ast.Term)expr.eval(this)));
    if (tail != null) { tail.eval(this); }
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public mobius.logic.lang.generic.ast.Application eval(
    final BinaryOp binaryOp, 
    final BinaryOp.Op op, 
    final Expr left, 
    final Expr right
  ) {
    final mobius.logic.lang.generic.ast.Term arg = 
      (mobius.logic.lang.generic.ast.Term)left.eval(this);
    arg.setNext((mobius.logic.lang.generic.ast.Term)right.eval(this));
    return mobius.logic.lang.generic.ast.Application.mk(
      mobius.logic.lang.generic.ast.Atom.mk(null, IdOfOp.get(op)),
      arg);
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(
    final ConstDecl constDecl, 
    final String id, 
    final Type type, 
    final boolean uniq, 
    final Declaration tail
  ) {
    fResult.add(Clause.mk(
      id,
      (mobius.logic.lang.generic.ast.Term)type.eval(this)));
    if (tail != null) { tail.eval(this); }
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(final DepType depType, final Type type, final Expr pred) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public mobius.logic.lang.generic.ast.Term eval(
    final Exprs exprs, 
    final Expr expr, 
    final Exprs tail
  ) {
    final mobius.logic.lang.generic.ast.Term r = 
      (mobius.logic.lang.generic.ast.Term)expr.eval(this);
    if (tail != null) { 
      r.setNext((mobius.logic.lang.generic.ast.Term)tail.eval(this));
    }
    return r;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(
    final Function function, 
    final Signature sig, 
    final Declaration tail
  ) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public mobius.logic.lang.generic.ast.Atom eval(
    final Identifiers identifiers, 
    final AtomId id, 
    final Identifiers tail
  ) {
    final mobius.logic.lang.generic.ast.Atom r = 
      (mobius.logic.lang.generic.ast.Atom)id.eval(this);
    if (tail != null) { 
      r.setNext((mobius.logic.lang.generic.ast.Term)tail.eval(this)); 
    }
    return r;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(final IndexedType indexedType, final Type param, final Type type) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(final MapType mapType, final TupleType idxType, final Type elemType) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(final PrimitiveType primitiveType, final PrimitiveType.Ptype ptype) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(
    final Procedure procedure, 
    final Signature sig, 
    final Specification spec, 
    final Declaration tail
  ) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(
    final Signature signature, 
    final String name, 
    final Declaration args, 
    final Declaration results, 
    final Identifiers typeVars
  ) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(
    final Specification specification, 
    final Identifiers typeVars, 
    final Specification.SpecType type, 
    final Expr expr, 
    final boolean free, 
    final Specification tail
  ) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(final TupleType tupleType, final Type type, final TupleType tail) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(final TypeDecl typeDecl, final String name, final Declaration tail) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(final UnaryOp unaryOp, final UnaryOp.Op op, final Expr e) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(final UserType userType, final String name) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(
    final VariableDecl variableDecl, 
    final String name, 
    final Type type, 
    final Identifiers typeVars, 
    final Declaration tail
  ) {
    assert false : "not implemented";
    return null;
  }
}
