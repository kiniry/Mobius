package freeboogie.tc;

import java.util.List;

import freeboogie.ast.Declaration;

/**
 * Builds a symbol table for a given AST, perhaps modifying
 * the AST slightly so that name resolution errors are
 * eliminated.
 *
 * The only modification that this class does at this time
 * is to introduce generics (type variables) on the innermost
 * declaration that contains a (type-) name error. For example,
 * the variable declaration {@code var h : [ref,&lt;x&gt;name]x}
 * is transformed into {@code var h&lt;x&gt; : [ref,&lt;x&gt;name]x}.
 */
public class ForgivingStb implements StbInterface {


  @Override
  public GlobalsCollector getGC() {
    assert false; // TODO
    return null;
  }

  @Override
  public SymbolTable getST() {
    assert false; // TODO
    return null;
  }

  @Override
  public Declaration getAST() {
    assert false;
    return null;
  }

  @Override
  public List<FbError> process(Declaration ast) {
    assert false; // TODO
    return null;
  }
}

