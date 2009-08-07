package freeboogie.astutil;

import java.io.PrintWriter;
import java.util.HashSet;

import com.google.common.collect.Sets;

import freeboogie.ast.*;

/** Prints in the Boogie2 format. */
public class Boogie2Printer extends PrettyPrinter {
  private HashSet<String> newKeywords;
  private Evaluator<Boolean> anyFinder;

  public Boogie2Printer(PrintWriter pw) {
    writer(pw);

    anyFinder = new AnyFinder();

    newKeywords = Sets.newHashSet();
    newKeywords.add("else");
    newKeywords.add("end");
    newKeywords.add("then");

    quantRep.put(AtomQuant.QuantType.FORALL, "forall<any> ");
  }

  public void process(Declaration ast) {
    printPrelude();
    ast.eval(anyFinder);
    ast.eval(this);
  }

  private void printPrelude() {
    say("type name"); semi();
    say("type ref"); semi();

    say("const unique null : ref"); semi();
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
    AtomFun atomFun, 
    String function, 
    TupleType types, 
    Exprs args
  ) {
    say(function);
    say("(");
    if (args != null) args.eval(this);
    say(")");
  }

  @Override
  public void see(
    AtomQuant atomQuant, 
    AtomQuant.QuantType quant, 
    Declaration vars, 
    Attribute attr, 
    Expr e
  ) {
    ++skipVar;
    say("(");
    if (quant == AtomQuant.QuantType.FORALL) {
      say("forall");
      if (anyFinder.get(vars)) {
        say("<"); say("any"); say(">");
      }
    } else say("exists");
    say(" ");
    vars.eval(this);
    say(" :: ");
    if (attr != null) attr.eval(this);
    e.eval(this);
    say(")");
    --skipVar;
  }

  @Override
  public void see(AtomId atomId, String id, TupleType types) {
    say(id);
  }

  @Override
  public void see(
    Axiom axiom, 
    Attribute attr,
    String name,
    Identifiers typeVars, 
    Expr expr, 
    Declaration tail
  ) {
    say("axiom ");
    expr.eval(this);
    semi();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(AtomCast atomCast, Expr e, Type type) {
    e.eval(this);
  }

  @Override
  public void see(IndexedType genericType, Type param, Type type) {
    type.eval(this);
  }

  @Override
  public void see(
    Signature signature, 
    String name, 
    Identifiers typeArgs,
    Declaration args, 
    Declaration results
  ) {
    ++skipVar;
    say(name);
    if (anyFinder.get(signature)) {
      say("<"); say("any"); say(">");
    }
    say("(");
    if (args != null) args.eval(this);
    say(")");
    if (results != null) {
      say(" returns (");
      results.eval(this);
      say(")");
    }
    --skipVar;
  }

  @Override
  public void see(
    Specification specification, 
    Identifiers tv, 
    Specification.SpecType type, 
    Expr expr, 
    boolean free, 
    Specification tail
  ) {
    if (free) say("free ");
    say(specRep.get(type));
    expr.eval(this);
    semi();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(
    VariableDecl variableDecl, 
    Attribute attr,
    String name, 
    Type type, 
    Identifiers typeArgs, 
    Declaration tail
  ) {
    if (skipVar==0) say("var ");
    say(name);
    say(" : ");
    if (typeArgs != null) {
      say("<");
      typeArgs.eval(this);
      say(">");
    }
    type.eval(this);
    if (skipVar>0) {
      if (tail != null) say(", ");
    } else semi();
    if (tail != null) tail.eval(this);
  }
  
}
