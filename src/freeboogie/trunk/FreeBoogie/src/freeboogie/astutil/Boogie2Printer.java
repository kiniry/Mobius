package freeboogie.astutil;

import java.io.PrintWriter;
import java.util.HashSet;

import com.google.common.collect.Sets;

import freeboogie.ast.*;

/** Prints in the Boogie2 format. */
public class Boogie2Printer extends PrettyPrinter {
  private HashSet<String> newKeywords;

  public Boogie2Printer(PrintWriter pw) {
    super(pw);

    newKeywords = Sets.newHashSet();
    newKeywords.add("else");
    newKeywords.add("end");
    newKeywords.add("then");

    typeRep.put(PrimitiveType.Ptype.NAME, "Name");
    typeRep.put(PrimitiveType.Ptype.REF, "Ref");
  }

  public void process(Declaration ast) {
    printPrelude();
    ast.eval(this);
  }

  private void printPrelude() {
    say("type Name"); semi();
    say("type Ref"); semi();
  }

  // This handles both block names and identifiers.
  // It is a bit of a hack because there's no guarantee that it doesn't
  // 'handle' too much.
  @Override protected void say(String s) {
    if (newKeywords.contains(s)) s = "id$" + s;
    super.say(s);
  }

  // === Overriden see methods ===


  @Override
  public void see(
    Axiom axiom, 
    String name,
    Identifiers typeVars, 
    Expr expr, 
    Declaration tail
  ) {
    // TODO: continue here
    say("axiom");
    say(" ");
    expr.eval(this);
    semi();
    if (tail != null) tail.eval(this);
  }
}
