package mobius.logic.lang.boogie;

//{{{ imports
import java.math.BigInteger;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

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

import mobius.logic.lang.generic.GType;
import mobius.logic.lang.generic.ast.Clause;
import mobius.logic.lang.generic.ast.ClauseList;
import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.generic.ast.Term;
//}}}


/**
 * Transforms Boogie into FOL. 
 * @author rgrig@
 */
public class GenericOfBoogie extends Evaluator<GenericAst> {
  private static final Map<BinaryOp.Op, String> binaryOpName =
    new HashMap<BinaryOp.Op, String>();

  private static final Map<UnaryOp.Op, String> unaryOpName =
    new HashMap<UnaryOp.Op, String>();

  static {
    binaryOpName.put(BinaryOp.Op.PLUS, "+");
    binaryOpName.put(BinaryOp.Op.MINUS, "-");
    binaryOpName.put(BinaryOp.Op.MUL, "*");
    binaryOpName.put(BinaryOp.Op.DIV, "/");
    binaryOpName.put(BinaryOp.Op.MOD, "%");
    binaryOpName.put(BinaryOp.Op.EQ, "=");
    binaryOpName.put(BinaryOp.Op.NEQ, "!=");
    binaryOpName.put(BinaryOp.Op.LT, "<");
    binaryOpName.put(BinaryOp.Op.LE, "<=");
    binaryOpName.put(BinaryOp.Op.GE, ">=");
    binaryOpName.put(BinaryOp.Op.GT, ">");
    binaryOpName.put(BinaryOp.Op.SUBTYPE, "<:");
    binaryOpName.put(BinaryOp.Op.EQUIV, "<->");
    binaryOpName.put(BinaryOp.Op.IMPLIES, "->");
    binaryOpName.put(BinaryOp.Op.AND, "and");
    binaryOpName.put(BinaryOp.Op.OR, "or");

    unaryOpName.put(UnaryOp.Op.MINUS, "-");
    unaryOpName.put(UnaryOp.Op.NOT, "bnot");
  }

  private final GenericTypeOfBoogie typeName = new GenericTypeOfBoogie();

  // TODO(rgrig): get axioms from the types that were processed
  public ClauseList getFrom(final Declaration boogie) {
    return (ClauseList) boogie.eval(this);
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
      case TRUE: id = "True"; break;
      case FALSE: id = "False"; break;
      case NULL: id = "Null"; break;
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
            (mobius.logic.lang.generic.ast.Atom.mk(
              null,
              ((Clause)(((ClauseList)vars.eval(this)).getList().getFirst()))
                .getId())),
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
    return combine(
      Clause.mk(
        name,
        (mobius.logic.lang.generic.ast.Term)expr.eval(this)),
        tail);
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
      mobius.logic.lang.generic.ast.Atom.mk(null, binaryOpName.get(op)),
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
    return combine(
      Clause.mk(
        id,
        (mobius.logic.lang.generic.ast.Term)type.eval(this)),
      tail);
  }

  /** {@inheritDoc} */
  // TODO(rgrig): handle the predicate
  @Override
  public Term eval(final DepType depType, final Type type, final Expr pred) {
    return (Term) type.eval(this);
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
    return combine(
      (Clause) sig.eval(this),
      tail);
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
  public Term eval(final IndexedType indexedType, final Type param, final Type type) {
    return evalType(indexedType);
  }

  /** {@inheritDoc} */
  @Override
  public Term eval(final MapType mapType, final TupleType idxType, final Type elemType) {
    return evalType(mapType);
  }

  /** {@inheritDoc} */
  @Override
  public Term eval(final PrimitiveType primitiveType, final PrimitiveType.Ptype ptype) {
    return evalType(primitiveType);
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(
    final Procedure procedure, 
    final Signature sig, 
    final Specification spec, 
    final Declaration tail
  ) {
    // TODO(rgrig): figure out how to translate procedures
    return tail == null? null : tail.eval(this);
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
    return Clause.mk(
      name,
      getType(args, getType(results, null)));
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
    return combine(
      Clause.mk(
        name,
        mobius.logic.lang.generic.ast.Atom.mk(null, GType.TopType)),
      tail);
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(final UnaryOp unaryOp, final UnaryOp.Op op, final Expr e) {
    return mobius.logic.lang.generic.ast.Application.mk(
      mobius.logic.lang.generic.ast.Atom.mk(null, unaryOpName.get(op)),
      (Term) e.eval(this));
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(final UserType userType, final String name) {
    return mobius.logic.lang.generic.ast.Atom.mk(null, name);
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
    return combine(
      Clause.mk(
        name,
        (Term) type.eval(this)),
      tail);
  }

  private ClauseList combine(Clause clause, Declaration tail) {
    ClauseList result = tail == null? 
      ClauseList.mk(new LinkedList<GenericAst>()) :
      (ClauseList) tail.eval(this);
    result.getList().addFirst(clause);
    return result;
  }

  private Term evalType(Type t) {
    return mobius.logic.lang.generic.ast.Atom.mk(null, t.eval(typeName));
  }

  private Term getType(Declaration d, Term tail) {
    VariableDecl vd = (VariableDecl) d;
    return mobius.logic.lang.generic.ast.Atom.mk(
      tail, 
      vd.getType().eval(typeName));
  }
}
