package freeboogie.tc;

import java.util.List;

import freeboogie.ast.Declaration;

/**
 * A symbol table builder (STB) constructs a symbol table
 * for an AST. It may change the AST to remove errors. The
 * errors that remain are returned.
 *
 * @author rgrig
 */
public interface StbInterface {
  /**
   * Builds a symbol table that can be later retrieved by a
   * call to {@code getST()}. The symbol table corresponds to
   * the AST returned by {@code getAST()}, which MAY be (slightly)
   * different from {@code ast}.
   */
  List<FbError> process(Declaration ast);

  /**
   * Returns the AST to which the symbol table returned by
   * {@code getST()} corresponds.
   */
  Declaration getAST();

  /**
   * Returns the latest built symbol table.
   */
  SymbolTable getST();

  /**
   * Returns the globals collector used during building of
   * the symbol table.
   */
  GlobalsCollector getGC();
}
