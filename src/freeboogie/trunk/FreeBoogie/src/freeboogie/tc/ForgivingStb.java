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
  
  // does the real work
  private StbInterface stb;

  /**
   * Constructs a forgiving symbol table builder.
   */
  public ForgivingStb() {
    stb = new SymbolTableBuilder();
  }

  @Override
  public GlobalsCollector getGC() {
    return stb.getGC();
  }

  @Override
  public SymbolTable getST() {
    return stb.getST();
  }

  @Override
  public Declaration getAST() {
    // TODO continue here
    return stb.getAST();
  }

  @Override
  public List<FbError> process(Declaration ast) {
    // TODO continue here
    return stb.process(ast);
  }
}

