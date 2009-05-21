package freeboogie.vcgen;

import java.util.*;

import genericutils.*;

import freeboogie.ast.*;
import freeboogie.tc.SymbolTable;

/**
 * Finds what identifiers appear in an expression and in what context.
 *
 * The call {@code ast.eval(rwsf)} returns a pair of {@code CSeq}
 * that contain the identifiers appearing in read context and those
 * that appear in write contexts. 
 *
 * NOTE: You can turn the {@code CSeq} into a set by iterating and
 * building a {@code HashSet}.
 *
 * TODO This is supposed to be more efficient than 
 * {@code freeboogie.astutil.VarCollector} but I'm not sure if
 * the extra complexity is worth it.
 *
 * @see freeboogie.astutil.VarCollector
 */
public class ReadWriteSetFinder 
extends AssociativeEvaluator<Pair<CSeq<VariableDecl>,CSeq<VariableDecl>>> {
  private SymbolTable st;
  private Deque<Boolean> context; // true = write, false = read

  public ReadWriteSetFinder(SymbolTable st) { 
    super(new PairAssocOp<CSeq<VariableDecl>,CSeq<VariableDecl>>(
      new CSeqAcc<VariableDecl>(), new CSeqAcc<VariableDecl>())); 
    this.st = st;
    context = new ArrayDeque<Boolean>();
    context.addFirst(false);
  }
 
  @Override
  public Pair<CSeq<VariableDecl>, CSeq<VariableDecl>> eval(AtomId atomId, String id, TupleType types) {
    Declaration d = st.ids.def(atomId);
    CSeq<VariableDecl> r, w;
    r = w = CSeq.mk();
    if (d instanceof VariableDecl) {
      VariableDecl vd = (VariableDecl)d;
      if (context.getFirst()) w = CSeq.mk(vd);
      else r = CSeq.mk(vd);
    }
    return memo(atomId, Pair.of(r, w));
  }

  @Override
  public Pair<CSeq<VariableDecl>, CSeq<VariableDecl>> eval(CallCmd callCmd, String procedure, TupleType types, Identifiers results, Exprs args) {
    assert !context.getFirst();
    Pair<CSeq<VariableDecl>, CSeq<VariableDecl>> r = assocOp.zero();
    if (results != null) {
      context.addFirst(true);
      r = assocOp.plus(r, results.eval(this));
      context.removeFirst();
    }
    if (args != null) 
      r = assocOp.plus(r, args.eval(this));
    return memo(callCmd, r);
  }

  @Override
  public Pair<CSeq<VariableDecl>, CSeq<VariableDecl>> eval(AssignmentCmd assignmentCmd, AtomId lhs, Expr rhs) {
    assert !context.getFirst();
    Pair<CSeq<VariableDecl>, CSeq<VariableDecl>> r = assocOp.zero();
    context.addFirst(true);
    r = assocOp.plus(r, lhs.eval(this));
    context.removeFirst();
    r = assocOp.plus(r, rhs.eval(this));
    return memo(assignmentCmd, r);
  }

  @Override
  public Pair<CSeq<VariableDecl>, CSeq<VariableDecl>> eval(HavocCmd havocCmd, Identifiers ids) {
    assert !context.getFirst();
    Pair<CSeq<VariableDecl>, CSeq<VariableDecl>> r = assocOp.zero();
    context.addFirst(true);
    if (ids != null) r = assocOp.plus(r, ids.eval(this));
    context.removeFirst();
    return memo(havocCmd, r);
  }

  @Override
  public Pair<CSeq<VariableDecl>, CSeq<VariableDecl>> eval(AtomMapSelect atomIdx, Atom atom, Exprs idx) {
    Pair<CSeq<VariableDecl>, CSeq<VariableDecl>> r = assocOp.zero();
    r = assocOp.plus(r, atom.eval(this));
    if (idx != null) {
      context.addFirst(false);
      r = assocOp.plus(r, idx.eval(this));
      context.removeFirst();
    }
    return memo(atomIdx, r);
  }
}
