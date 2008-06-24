package freeboogie.vcgen;

import java.util.*;

import freeboogie.ast.*;
import freeboogie.tc.SymbolTable;
import freeboogie.util.*;

public class ReadWriteSetFinder 
extends AssociativeEvaluator<Pair<CSeq<VariableDecl>,CSeq<VariableDecl>>> {
  private SymbolTable st;
  private Deque<Boolean> context; // true = write, false = read

  public ReadWriteSetFinder(SymbolTable st) { 
    super(new PairAssocOp<CSeq<VariableDecl>,CSeq<VariableDecl>>(
      new CSeqAcc<VariableDecl>(), new CSeqAcc<VariableDecl>())); 
    this.st = st;
    context.addFirst(true);
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
    return new Pair<CSeq<VariableDecl>, CSeq<VariableDecl>>(r, w);
  }
}
