package freeboogie.astutil;

import java.io.PrintWriter;
import java.util.HashSet;

import com.google.common.collect.Sets;

import freeboogie.ast.*;

/** Prints in the Boogie2 format. */
public class Boogie2Printer extends PrettyPrinter {
  private HashSet<String> newKeywords;
  private int indexedTypeCnt;

  public Boogie2Printer(PrintWriter pw) {
    super(pw);

    indexedTypeCnt = 0;

    newKeywords = Sets.newHashSet();
    newKeywords.add("else");
    newKeywords.add("end");
    newKeywords.add("then");

    typeRep.put(PrimitiveType.Ptype.ANY, "Any");
    typeRep.put(PrimitiveType.Ptype.NAME, "Name");
    typeRep.put(PrimitiveType.Ptype.REF, "Ref");
  }

  public void process(Declaration ast) {
    printPrelude();
    ast.eval(this);
  }

  private void printPrelude() {
    say("type Any"); semi();
    say("type Name _"); semi();
    say("type Ref"); semi();
    say("type UnitType"); semi();

    say("const unique null : Ref"); semi();
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
  public void see(AtomId atomId, String id, TupleType types) {
    say(id);
  }

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

  @Override
  public void see(AtomCast atomCast, Expr e, Type type) {
    e.eval(this);
  }

  @Override
  public void see(IndexedType genericType, Type param, Type type) {
    ++indexedTypeCnt;
    type.eval(this);
    --indexedTypeCnt;
    say(" ");
    say("("); param.eval(this); say(")");
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
  public void see(PrimitiveType primitiveType, PrimitiveType.Ptype ptype) {
    say(typeRep.get(ptype));
    if (ptype == PrimitiveType.Ptype.NAME && indexedTypeCnt == 0)
      say(" UnitType");
  }

  @Override
  public void see(
    VariableDecl variableDecl, 
    String name, 
    Type type, 
    Identifiers typeVars, 
    Declaration tail
  ) {
    if (skipVar==0) say("var ");
    say(name);
    say(" : ");
    if (typeVars != null) {
      say("<");
      typeVars.eval(this);
      say(">");
    }
    type.eval(this);
    if (skipVar>0) {
      if (tail != null) say(", ");
    } else semi();
    if (tail != null) tail.eval(this);
  }
  
}
