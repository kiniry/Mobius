package freeboogie.vcgen;

import java.util.ArrayList;

import freeboogie.ast.*;
import freeboogie.backend.Sort;
import freeboogie.backend.TermBuilder;

/**
 * Registers symbols corresponding to the functions in Boogie.
 */
public class FunctionRegisterer extends Transformer {
  private TermBuilder builder;
  private ArrayList<Sort> argSorts = new ArrayList<Sort>();

  public void setBuilder(TermBuilder builder) {
    this.builder = builder;
  }

  public void process(Declaration ast) {
    if (ast == null || builder == null) return;
    ast.eval(this);
  }

  @Override
  public void see(Function function, Signature sig, Declaration tail) {
    argSorts.clear();
    getArgSorts(sig.getArgs());
    Type resultType = ((VariableDecl)sig.getResults()).getType();
    Sort resultSort = Sort.of(resultType);
    builder.def(sig.getName(), argSorts.toArray(new Sort[0]), resultSort);
    if (tail != null) tail.eval(this);
  }

  // === helpers ===
  private void getArgSorts(Declaration args) {
    if (!(args instanceof VariableDecl)) return;
    VariableDecl vd = (VariableDecl)args;
    argSorts.add(Sort.of(vd.getType()));
    getArgSorts(vd.getTail());
  }
}
