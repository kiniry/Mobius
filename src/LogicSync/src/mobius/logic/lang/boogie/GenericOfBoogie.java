package mobius.logic.lang.boogie;

//{{{ imports
import java.math.BigInteger;

import freeboogie.ast.Atom;
import freeboogie.ast.AtomCast;
import freeboogie.ast.AtomFun;
import freeboogie.ast.AtomId;
import freeboogie.ast.AtomLit;
import freeboogie.ast.AtomMapSelect;
import freeboogie.ast.AtomNum;
import freeboogie.ast.AtomOld;
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
import mobius.logic.lang.generic.ast.GenericAst;
//}}}


/**
 * Transforms Boogie into FOL.
 * @author rgrig@
 */
public class GenericOfBoogie extends Evaluator<GenericAst> {
  /** {@inheritDoc} */
  @Override
  public GenericAst eval(
    final AtomCast atomCast, 
    final Expr e, 
    final Type type
  ) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(
    final AtomFun atomFun, 
    final String function, 
    final TupleType types, 
    final Exprs args
  ) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(
    final AtomId atomId, 
    final String id, 
    final TupleType types
  ) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(final AtomLit atomLit, final AtomLit.AtomType val) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(final AtomMapSelect atomMapSelect, final Atom atom, final Exprs idx) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(final AtomNum atomNum, final BigInteger val) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(final AtomOld atomOld, final Expr e) {
    assert false : "not implemented";
    return null;
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
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(
    final Axiom axiom, 
    final Identifiers typeVars, 
    final Expr expr, 
    final Declaration tail
  ) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public GenericAst eval(
    final BinaryOp binaryOp, 
    final BinaryOp.Op op, 
    final Expr left, 
    final Expr right
  ) {
    assert false : "not implemented";
    return null;
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
    assert false : "not implemented";
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
  public GenericAst eval(final Exprs exprs, final Expr expr, final Exprs tail) {
    assert false : "not implemented";
    return null;
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
  public GenericAst eval(
    final Identifiers identifiers, 
    final AtomId id, 
    final Identifiers tail
  ) {
    assert false : "not implemented";
    return null;
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
