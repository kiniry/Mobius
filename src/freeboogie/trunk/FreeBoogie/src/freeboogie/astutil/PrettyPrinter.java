package freeboogie.astutil;

import java.io.IOException;
import java.io.Writer;
import java.math.BigInteger;
import java.util.HashMap;

import com.google.common.collect.Maps;

import freeboogie.Main;
import freeboogie.ast.*;
import freeboogie.cli.FbCliOptionsInterface;
import genericutils.Err;

/**
 * Prints AST nodes in a readable (and parseable) way.
 *
 * @author rgrig 
 */
@SuppressWarnings("unused") // lots of unused parameters
public class PrettyPrinter extends Transformer {
  private int indent = 2; // indentation spaces
  
  private Writer writer; // where the output is sent
  
  /**
   * The nesting level:
   * Should be zero when I start and when I finish printing.
   */ 
  protected int indentLevel;
  
  protected int skipVar; // if >0 then skip "var "

  // should types in a TupleType be prefixed by "`"?
  private boolean prefixByBq;
  
  // ready made strings to be printed for enums
  protected HashMap<AssertAssumeCmd.CmdType,String> cmdRep ;
  protected HashMap<AtomLit.AtomType,String> atomRep;
  protected HashMap<AtomQuant.QuantType,String> quantRep;
  protected HashMap<BinaryOp.Op,String> binRep;
  protected HashMap<PrimitiveType.Ptype,String> typeRep;
  protected HashMap<Specification.SpecType,String> specRep;
  protected HashMap<UnaryOp.Op,String> unRep;
  
  private void initConstants() {
  }
  
  /**
   * Initialize the pretty printer with a writer.
   * @param w the writer
   */
  public PrettyPrinter(Writer w) {
    assert w != null;
    writer = w;
    indent = 2;
    indentLevel = 0;
    skipVar = 0;
    prefixByBq = false;
  
    cmdRep = Maps.newHashMap();
    atomRep = Maps.newHashMap();
    quantRep = Maps.newHashMap();
    binRep = Maps.newHashMap();
    typeRep = Maps.newHashMap();
    specRep = Maps.newHashMap();
    unRep = Maps.newHashMap();

    cmdRep.put(AssertAssumeCmd.CmdType.ASSERT, "assert ");
    cmdRep.put(AssertAssumeCmd.CmdType.ASSUME, "assume ");
    atomRep.put(AtomLit.AtomType.FALSE, "false");
    atomRep.put(AtomLit.AtomType.TRUE, "true");
    atomRep.put(AtomLit.AtomType.NULL, "null");
    quantRep.put(AtomQuant.QuantType.EXISTS, "exists ");
    quantRep.put(AtomQuant.QuantType.FORALL, "forall ");
    binRep.put(BinaryOp.Op.AND, " && ");
    binRep.put(BinaryOp.Op.DIV, " / ");
    binRep.put(BinaryOp.Op.EQ, " == ");
    binRep.put(BinaryOp.Op.EQUIV, " <==> ");
    binRep.put(BinaryOp.Op.GE, " >= ");
    binRep.put(BinaryOp.Op.GT, " > ");
    binRep.put(BinaryOp.Op.IMPLIES, " ==> ");
    binRep.put(BinaryOp.Op.LE, " <= ");
    binRep.put(BinaryOp.Op.LT, " < ");
    binRep.put(BinaryOp.Op.MINUS, " - ");
    binRep.put(BinaryOp.Op.MOD, " % ");
    binRep.put(BinaryOp.Op.MUL, " * ");
    binRep.put(BinaryOp.Op.NEQ, " != ");
    binRep.put(BinaryOp.Op.OR, " || ");
    binRep.put(BinaryOp.Op.PLUS, " + ");
    binRep.put(BinaryOp.Op.SUBTYPE, " <: ");
    typeRep.put(PrimitiveType.Ptype.ANY, "any");
    typeRep.put(PrimitiveType.Ptype.BOOL, "bool");
    typeRep.put(PrimitiveType.Ptype.INT, "int");
    typeRep.put(PrimitiveType.Ptype.NAME, "name");
    typeRep.put(PrimitiveType.Ptype.REF, "ref");
    typeRep.put(PrimitiveType.Ptype.ERROR, "?");
    specRep.put(Specification.SpecType.ENSURES, "ensures ");
    specRep.put(Specification.SpecType.MODIFIES, "modifies ");
    specRep.put(Specification.SpecType.REQUIRES, "requires ");
    unRep.put(UnaryOp.Op.MINUS, "-");
    unRep.put(UnaryOp.Op.NOT, "!");
  }
  
  /** Swallow exceptions. */
  protected void say(String s) {
    try {
      writer.write(s);
    } catch (IOException e) {
      Err.help("Can't pretty print. Nevermind.");
    }
  }
  
  /** Send a newline to the writer. */
  protected void nl() {
    say("\n"); // TODO: handle Windows?
    for (int i = indent * indentLevel; i > 0; --i) say(" ");
  }
  
  /** End command. */
  protected void semi() {
    say(";"); nl();
  }
  
  // === the visiting methods ===
  
  @Override
  public void see(MapType arrayType, TupleType idxType, Type elemType) {
    say("[");
    assert !prefixByBq;
    idxType.eval(this);
    say("]");
    elemType.eval(this);
  }

  @Override
  public void see(
    AssertAssumeCmd assertAssumeCmd, 
    AssertAssumeCmd.CmdType type, 
    Identifiers typeVars, 
    Expr expr
  ) {
    say(cmdRep.get(type));
    if (typeVars != null) {
      say("<");
      typeVars.eval(this);
      say(">");
    }
    expr.eval(this);
    say(";");
  }

  @Override
  public void see(AssignmentCmd assignmentCmd, AtomId lhs, Expr rhs) {
    lhs.eval(this);
    say(" := ");
    rhs.eval(this);
    say(";");
  }

  @Override
  public void see(AtomCast atomCast, Expr e, Type type) {
    say("cast(");
    e.eval(this);
    say(", ");
    type.eval(this);
    say(")");
  }

  @Override
  public void see(
    AtomFun atomFun, 
    String function, 
    TupleType types, 
    Exprs args
  ) {
    say(function);
    if (types != null) {
      say("<");
      assert !prefixByBq;
      prefixByBq = true;
      types.eval(this);
      prefixByBq = false;
      say(">");
    }
    say("(");
    if (args != null) args.eval(this);
    say(")");
  }

  @Override
  public void see(AtomId atomId, String id, TupleType types) {
    say(id);
    if (types != null) {
      say("<");
      assert !prefixByBq;
      prefixByBq = true;
      types.eval(this);
      prefixByBq = false;
      say(">");
    }
  }

  @Override
  public void see(AtomMapSelect atomMapSelect, Atom atom, Exprs idx) {
    atom.eval(this);
    say("[");
    idx.eval(this);
    say("]");
  }

  @Override
  public void see(AtomMapUpdate atomMapUpdate, Atom atom, Exprs idx, Expr val) {
    atom.eval(this);
    say("[");
    idx.eval(this);
    say(" := ");
    val.eval(this);
    say("]");
  }

  @Override
  public void see(AtomLit atomLit, AtomLit.AtomType val) {
    say(atomRep.get(val));
  }

  @Override
  public void see(AtomNum atomNum, BigInteger val) {
    say(val.toString());
  }

  @Override
  public void see(AtomOld atomOld, Expr e) {
    say("old(");
    e.eval(this);
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
    say(quantRep.get(quant));
    vars.eval(this);
    say(" :: ");
    if (attr != null) attr.eval(this);
    e.eval(this);
    say(")");
    --skipVar;
  }

  @Override
  public void see(
    Axiom axiom, 
    Attribute attr,
    String name,
    Identifiers typeArgs, 
    Expr expr, 
    Declaration tail
  ) {
    say("axiom");
    if (Main.opt.getBoogieVersion() == FbCliOptionsInterface.BoogieVersion.TWO) {
      say(" ");
      say(name);
    }
    if (typeArgs != null) {
      say("<");
      typeArgs.eval(this);
      say(">");
    }
    if (Main.opt.getBoogieVersion() == FbCliOptionsInterface.BoogieVersion.TWO) {
      say(":");
    }
    say(" ");
    expr.eval(this); semi();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(BinaryOp binaryOp, BinaryOp.Op op, Expr left, Expr right) {
    say("(");
    left.eval(this);
    say(binRep.get(op));
    right.eval(this);
    say(")");
  }

  @Override
  public void see(
    Block block, 
    String name, 
    Command cmd, 
    Identifiers succ, 
    Block tail
  ) {
    say(name);
    say(":");
    if (cmd != null) {
      say(" ");
      cmd.eval(this);
    }
    say(" ");
    if (succ == null) {
      say("return");
    } else {
      say("goto ");
      succ.eval(this);
    }
    semi();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(Body body, Declaration vars, Block blocks) {
    say(" {");
    ++indentLevel; nl();
    if (vars != null) vars.eval(this);
    if (blocks != null) blocks.eval(this);
    --indentLevel; nl();
    say("}");
    nl();
  }

  @Override
  public void see(
    CallCmd callCmd, 
    String procedure, 
    TupleType types, 
    Identifiers results, 
    Exprs args
  ) {
    say("call ");
    if (results != null) {
      results.eval(this);
      say(" := ");
    }
    say(procedure);
    if (types != null) {
      say("<");
      assert !prefixByBq;
      prefixByBq = true;
      types.eval(this);
      prefixByBq = false;
      say(">");
    }
    say("(");
    if (args != null) args.eval(this);
    say(");");
  }

  @Override
  public void see(
    ConstDecl constDecl, 
    Attribute attr,
    String id, 
    Type type, 
    boolean uniq, 
    Declaration tail
  ) {
    say("const ");
    if (attr != null) {
      attr.eval(this);
      say(" ");
    }
    if (uniq) say("unique ");
    say(id);
    say(" : ");
    type.eval(this);
    semi();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(DepType depType, Type type, Expr pred) {
    type.eval(this);
    say(" where ");
    pred.eval(this);
  }

  @Override
  public void see(Exprs exprs, Expr expr, Exprs tail) {
    expr.eval(this);
    if (tail != null) {
      say(", ");
      tail.eval(this);
    }
  }

  @Override
  public void see(
    Function function,
    Attribute attr,
    Signature sig,
    Declaration tail
  ) {
    say("function ");
    if (attr != null) {
      attr.eval(this);
      say(" ");
    }
    sig.eval(this);
    semi();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(IndexedType genericType, Type param, Type type) {
    say("<");
    param.eval(this);
    say(">");
    type.eval(this);
  }

  @Override
  public void see(HavocCmd havocCmd, Identifiers ids) {
    say("havoc ");
    ids.eval(this);
    say(";");
  }

  @Override
  public void see(Identifiers identifiers, AtomId id, Identifiers tail) {
    id.eval(this);
    if (tail != null) {
      say(", ");
      tail.eval(this);
    }
  }

  @Override
  public void see(
    Implementation implementation, 
    Attribute attr,
    Signature sig, 
    Body body, 
    Declaration tail
  ) {
    say("implementation ");
    if (attr != null) {
      attr.eval(this);
      say(" ");
    }
    sig.eval(this);
    body.eval(this);
    nl();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(
    PrimitiveType primitiveType,
    PrimitiveType.Ptype ptype,
    int bits
  ) {
    say(typeRep.get(ptype));
  }

  @Override
  public void see(
    Procedure procedure, 
    Attribute attr,
    Signature sig, 
    Specification spec, 
    Declaration tail
  ) {
    say("procedure ");
    if (attr != null) {
      attr.eval(this);
      say(" ");
    }
    sig.eval(this);
    say(";");
    if (spec != null) {
      ++indentLevel; nl();
      spec.eval(this);
      --indentLevel; nl();
    }
    nl();
    if (tail != null) tail.eval(this);
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
    if (typeArgs != null) {
      say("<");
      typeArgs.eval(this);
      say(">");
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
    if (tv != null) {
      say("<");
      tv.eval(this);
      say(">");
    }
    expr.eval(this);
    semi();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(TupleType tupleType, Type type, TupleType tail) {
    if (prefixByBq) say("`");
    type.eval(this);
    if (tail != null) {
      say(", ");
      tail.eval(this);
    }
  }

  @Override
  public void see(
    TypeDecl typeDecl,
    Attribute attr,
    String name,
    Identifiers typeArgs,
    boolean finite,
    Type type,
    Declaration tail
  ) {
    say("type ");
    if (attr != null) {
      attr.eval(this);
      say(" ");
    }
    if (finite && 
      Main.opt.getBoogieVersion() == FbCliOptionsInterface.BoogieVersion.TWO) {
      say("finite ");
    }
    say(name);
    // TODO: print space-separated typeArgs
    if (type != null) {
      say(" = ");
      type.eval(this);
    }
    semi();
    tail.eval(this);
  }

  @Override
  public void see(UnaryOp unaryOp, UnaryOp.Op op, Expr e) {
    say(unRep.get(op));
    e.eval(this);
  }

  @Override
  public void see(UserType userType, String name, TupleType typeArgs) {
    say(name);
    // TODO: print space-separated typeArgs
  }

  @Override
  public void see(
    VariableDecl variableDecl, 
    Attribute attr,
    String name, 
    Type type, 
    Identifiers typeVars, 
    Declaration tail
  ) {
    if (skipVar==0) say("var ");
    if (attr != null) {
      attr.eval(this);
      say(" ");
    }
    say(name);
    if (typeVars != null) {
      say("<");
      typeVars.eval(this);
      say(">");
    }
    say(" : ");
    type.eval(this);
    if (skipVar>0) {
      if (tail != null) say(", ");
    } else semi();
    if (tail != null) tail.eval(this);
  }
  
  @Override
  public void see(Attribute trigger, String type, Exprs exprs, Attribute tail) {
    say("{");
    say(":"); say(type);
    say(" ");
    if (exprs != null) exprs.eval(this);
    say("} ");
    if (tail != null) tail.eval(this);
  }
}
