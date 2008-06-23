package freeboogie.vcgen;

import java.util.*;

import freeboogie.ast.*;
import freeboogie.tc.SymbolTable;
import freeboogie.util.*;

public class ReadWriteSetFinder 
extends AssociativeEvaluator<Pair<Set<VariableDecl>,Set<VariableDecl>>> {
  private SymbolTable st;
  private Deque<Boolean> context; // true = write, false = read

  public ReadWriteSetFinder(SymbolTable st) { 
    super(new PairAssocOp<Set<VariableDecl>,Set<VariableDecl>>(
      new SetUnion<VariableDecl>(), new SetUnion<VariableDecl>())); 
    this.st = st;
    context.addFirst(true);
  }
  
  @Override
  public Pair<Set<VariableDecl>, Set<VariableDecl>> eval(AtomId atomId, String id, TupleType types) {
    Pair<Set<VariableDecl>, Set<VariableDecl>> r = 
      new Pair<Set<VariableDecl>, Set<VariableDecl>>(
        new TreeSet<VariableDecl>(), new TreeSet<VariableDecl>());
    Declaration d = st.ids.def(atomId);
    if (d instanceof VariableDecl) {
      VariableDecl vd = (VariableDecl)d;
      if (context.peekFirst())
        r.second.add(vd);
      else
        r.first.add(vd);
    }
    return r;
  }
}
