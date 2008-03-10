package freeboogie.astutil;

import java.util.*;
import freeboogie.ast.*;
import freeboogie.tc.SymbolTable;

/**
 * Collects the declarations of variables that are read or written.
 */
public class VarCollector extends Transformer {
  // the symbol table used to find declarations
  private SymbolTable st;

  // read/write variables
  private Set<Declaration> rv, wv;

  public void VarCollector(SymbolTable st) {
    this.st = st;
  }

  public void process(Ast ast) {
    rv = new HashSet<Declaration>();
    wv = new HashSet<Declaration>();
    ast.eval(this);
  }

  public Set<Declaration> readVar() { return rv; }
  public Set<Declaration> writeVar() { return wv; }


  @Override
  public void see(AtomId atomId, String id) { 
    rv.add(st.ids.def(atomId)); 
  }

  @Override
  public void see(AssignmentCmd assignmentCmd, Expr lhs, Expr rhs) {
    if (lhs instanceof AtomId)
      wv.add(st.ids.def((AtomId)lhs));
    else if (lhs instanceof AtomIdx) {
      AtomIdx ai = (AtomIdx) lhs;
      if (ai.getAtom() instanceof AtomId)
        wv.add(st.ids.def((AtomId)ai.getAtom()));
      ai.getIdx().eval(this);
    }
    rhs.eval(this);
  }
}

