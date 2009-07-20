package freeboogie.vcgen;

import java.util.ArrayList;

import freeboogie.ast.*;
import freeboogie.backend.Sort;
import freeboogie.backend.TermBuilder;
import freeboogie.tc.SymbolTable;
import freeboogie.tc.TcInterface;
import freeboogie.tc.TypeUtils;

/**
 * Registers symbols corresponding to the functions in Boogie.
 *
 * All function symbols are prefixed by "funX_" where X is either
 * I, B, or T, depending on whether the return type is int, bool,
 * or something else. If the return type is a type variable
 * then the name of the function is registered with all three
 * prefixes.
 */
public class FunctionRegisterer extends Transformer {
  private static Sort[] sortArray = new Sort[0];

  private TermBuilder builder;
  private ArrayList<Sort> argSorts = new ArrayList<Sort>();
  private SymbolTable st;

  public void setBuilder(TermBuilder builder) {
    this.builder = builder;
  }

  @Override
  public Declaration process(Declaration ast, TcInterface tc) {
    st = tc.getST();
    ast.eval(this);
    return ast;
  }

  @Override
  public void see(
    Function function,
    Attribute attr,
    Signature sig,
    Declaration tail
  ) {
    argSorts.clear();
    getArgSorts(sig.getArgs());
    Sort[] asa = argSorts.toArray(sortArray);
    Type rt = ((VariableDecl)sig.getResults()).getType();
    if (TypeUtils.isInt(rt) || isTypeVar(rt))
      builder.def("funI_" + sig.getName(), asa, Sort.INT);
    if (TypeUtils.isBool(rt) || isTypeVar(rt))
      builder.def("funB_" + sig.getName(), asa, Sort.BOOL);
    if (!TypeUtils.isInt(rt) && !TypeUtils.isBool(rt))
      builder.def("funT_" + sig.getName(), asa, Sort.TERM);
    if (tail != null) tail.eval(this);
  }

  // === helpers ===
  private void getArgSorts(Declaration args) {
    if (!(args instanceof VariableDecl)) return;
    VariableDecl vd = (VariableDecl)args;
    argSorts.add(Sort.of(vd.getType()));
    getArgSorts(vd.getTail());
  }

  private boolean isTypeVar(Type t) {
    if (!(t instanceof UserType)) return false;
    UserType ut = (UserType)t;
    return st.typeVars.def(ut) != null;
  }
}
