package freeboogie.astutil;

import java.util.HashSet;
import java.util.LinkedHashSet;

import freeboogie.ast.Ast;
import freeboogie.ast.Transformer;

// DBG
import java.io.PrintWriter;

/** Checks if AST is a tree (as opposed to a dag). */
public class TreeChecker extends Transformer {
  private HashSet<Ast> seen;
  private boolean duplicateFound;

  public TreeChecker() {
    seen = new LinkedHashSet<Ast>(100003);
  }

  public boolean isTree(Ast ast) {
    seen.clear();
    duplicateFound = false;
    ast.eval(this);
    System.out.println("seen size = " + seen.size());
    return !duplicateFound;
  }

  @Override
  public void enterNode(Ast ast) {
    /* DBG
    if (seen.contains(ast)) {
      System.out.println("=== BEGIN SHARED");
      PrintWriter pw = new PrintWriter(System.out);
      PrettyPrinter pp = new PrettyPrinter(pw);
      ast.eval(pp);
      pw.flush();
      System.out.println();
      System.out.println(ast.loc());
      System.out.println("=== END SHARED");
    }
    */
    duplicateFound |= !seen.add(ast);
  }
}
