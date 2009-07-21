package freeboogie.astutil;

import java.util.*;
import freeboogie.ast.*;
import freeboogie.tc.SymbolTable;

/**
 * Collects the declarations of variables that are read or written.
 *
 * TODO Decide whether I should transition to this from 
 * {@code ReadWriteSetFinder}.
 *
 * @author rgrig
 * @see freeboogie.vcgen.ReadWriteSetFinder
 */
public class VarCollector extends Transformer {
  // the symbol table used to find declarations
  private SymbolTable st;

  // read/write variables
  private Set<Declaration> rv, wv;

  public VarCollector(SymbolTable st) {
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
  public void see(AtomId atomId, String id, TupleType types) { 
    assert types == null; // TODO
    rv.add(st.ids.def(atomId)); 
  }

  @Override
  public void see(AssignmentCmd assignmentCmd, AtomId lhs, Expr rhs) {
    wv.add(st.ids.def(lhs));
    rhs.eval(this);
  }
}

