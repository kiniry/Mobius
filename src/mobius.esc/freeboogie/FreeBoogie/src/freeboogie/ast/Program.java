package freeboogie.ast;

/** Structure holding the AST plus some meta-data. */
public class Program {
  public final Declaration ast;
  public final String fileName;

  public Program(Ast ast, String fileName) {
    this.ast = (Declaration)ast;
    this.fileName = fileName;
  }
}
