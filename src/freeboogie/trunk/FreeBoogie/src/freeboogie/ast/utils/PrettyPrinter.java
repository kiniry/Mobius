/** Public domain. */

package freeboogie.ast.utils;

import java.io.PrintWriter;
import java.io.Writer;
import java.math.BigInteger;
import java.util.HashMap;

import freeboogie.ast.*;

/**
 * Prints AST nodes in a readable (and parseable) way.
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
@SuppressWarnings("unused") // lots of unused parameters
public class PrettyPrinter extends Transformer {
  private static final int indent = 2; // indentation spaces
  
  private PrintWriter writer; // where the output is sent
  
  /**
   * The nesting level:
   * Should be zero when I start and when I finish printing.
   */ 
  private int indentLevel;
  
  private int skipVar; // if >0 then skip "var "
  
  // ready made strings to be printed for enums
  private static final HashMap<AssertAssumeCmd.CmdType,String> cmdRep 
    = new HashMap<AssertAssumeCmd.CmdType,String>(5);
  private static final HashMap<AtomLit.AtomType,String> atomRep
    = new HashMap<AtomLit.AtomType,String>(5);
  private static final HashMap<AtomQuant.QuantType,String> quantRep
    = new HashMap<AtomQuant.QuantType,String>(5);
  private static final HashMap<BinaryOp.Op,String> binRep
    = new HashMap<BinaryOp.Op,String>(29);
  private static final HashMap<BlockEnd.BlockType,String> bendRep
    = new HashMap<BlockEnd.BlockType,String>(5);
  private static final HashMap<PrimitiveType.Ptype,String> typeRep
    = new HashMap<PrimitiveType.Ptype,String>(11);
  private static final HashMap<Specification.SpecType,String> specRep
    = new HashMap<Specification.SpecType,String>(5);
  private static final HashMap<UnaryOp.Op,String> unRep
    = new HashMap<UnaryOp.Op,String>(5);
  
  static {
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
    bendRep.put(BlockEnd.BlockType.GOTO, "goto ");
    bendRep.put(BlockEnd.BlockType.RETURN, "return");
    typeRep.put(PrimitiveType.Ptype.ANY, "any");
    typeRep.put(PrimitiveType.Ptype.BOOL, "bool");
    typeRep.put(PrimitiveType.Ptype.INT, "int");
    typeRep.put(PrimitiveType.Ptype.NAME, "name");
    typeRep.put(PrimitiveType.Ptype.REF, "ref");
    specRep.put(Specification.SpecType.ENSURES, "ensures ");
    specRep.put(Specification.SpecType.MODIFIES, "modifies ");
    specRep.put(Specification.SpecType.REQUIRES, "requires ");
    unRep.put(UnaryOp.Op.MINUS, "-");
    unRep.put(UnaryOp.Op.NOT, "!");
  }
  
  /**
   * Initialize the pretty printer with a writer.
   * @param w the writer
   */
  public PrettyPrinter(PrintWriter w) {
    assert w != null;
    writer = w;
    indentLevel = 0;
    skipVar = 0;
  }
  
  /** Send a newline to the writer. */
  private void nl() {
    writer.println();
    for (int i = indent * indentLevel; i > 0; --i)
      writer.print(' ');
  }
  
  // === the visiting methods ===
  
  @Override
  public void see(ArrayType arrayType, Type rowType, Type colType, Type elemType) {
    writer.print('[');
    rowType.eval(this);
    if (colType != null) {
      writer.print(", ");
      colType.eval(this);
    }
    writer.print(']');
    elemType.eval(this);
  }

  @Override
  public void see(AssertAssumeCmd assertAssumeCmd, AssertAssumeCmd.CmdType type, Expr expr) {
    writer.print(cmdRep.get(type));
    expr.eval(this);
    writer.print(';');
    nl();
  }

  @Override
  public void see(AssignmentCmd assignmentCmd, Expr lhs, Expr rhs) {
    lhs.eval(this);
    writer.print(" := ");
    rhs.eval(this);
    writer.print(';');
    nl();
  }

  @Override
  public void see(AtomCast atomCast, Expr e, Type type) {
    writer.print("cast(");
    e.eval(this);
    writer.print(", ");
    type.eval(this);
    writer.print(')');
  }

  @Override
  public void see(AtomFun atomFun, String function, Exprs args) {
    writer.print(function);
    writer.print('(');
    if (args != null) args.eval(this);
    writer.print(')');
  }

  @Override
  public void see(AtomId atomId, String id) {
    writer.print(id);
  }

  @Override
  public void see(AtomIdx atomIdx, Atom atom, Index idx) {
    atom.eval(this);
    idx.eval(this);
  }

  @Override
  public void see(AtomLit atomLit, AtomLit.AtomType val) {
    writer.print(atomRep.get(val));
  }

  @Override
  public void see(AtomNum atomNum, BigInteger val) {
    writer.print(val);
  }

  @Override
  public void see(AtomOld atomOld, Expr e) {
    writer.print("old(");
    e.eval(this);
    writer.print(')');
  }

  @Override
  public void see(AtomQuant atomQuant, AtomQuant.QuantType quant, Declaration vars, Trigger trig, Expr e) {
    ++skipVar;
    writer.print('(');
    writer.print(quantRep.get(quant));
    vars.eval(this);
    writer.print(" :: ");
    if (trig != null) trig.eval(this);
    e.eval(this);
    writer.print(')');
    --skipVar;
  }

  @Override
  public void see(Axiom axiom, Expr expr, Declaration tail) {
    writer.print("axiom ");
    expr.eval(this);
    writer.print(';');
    nl();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(BinaryOp binaryOp, BinaryOp.Op op, Expr left, Expr right) {
    writer.print('(');
    left.eval(this);
    writer.print(binRep.get(op));
    right.eval(this);
    writer.print(')');
  }

  @Override
  public void see(Block block, String name, Commands cmds, BlockEnd end, Block tail) {
    writer.print(name);
    writer.print(':');
    ++indentLevel; nl();
    if (cmds != null) cmds.eval(this);
    end.eval(this);
    --indentLevel; nl();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(BlockEnd blockEnd, BlockEnd.BlockType type, Identifiers dest) {
    writer.print(bendRep.get(type));
    if (dest != null) dest.eval(this);
    writer.print(';');
    nl();
  }

  @Override
  public void see(Body body, Declaration vars, Block blocks) {
    writer.print(" {");
    ++indentLevel; nl();
    if (vars != null) vars.eval(this);
    if (blocks != null) blocks.eval(this);
    --indentLevel; nl();
    writer.print("}");
    nl();
  }

  @Override
  public void see(CallCmd callCmd, String function, Identifiers results, Exprs args) {
    writer.print("call ");
    if (results != null) {
      results.eval(this);
      writer.print(" := ");
    }
    writer.print(function);
    writer.print('(');
    if (args != null) args.eval(this);
    writer.print(");");
    nl();
  }

  @Override
  public void see(Commands commands, Command cmd, Commands tail) {
    cmd.eval(this);
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(ConstDecl constDecl, String id, Type type, Declaration tail) {
    writer.print("const ");
    writer.print(id);
    writer.print(" : ");
    type.eval(this);
    writer.print(';');
    nl();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(DepType depType, Type type, Expr pred) {
    type.eval(this);
    writer.print(" where ");
    pred.eval(this);
  }

  @Override
  public void see(Exprs exprs, Expr expr, Exprs tail) {
    expr.eval(this);
    if (tail != null) {
      writer.print(", ");
      tail.eval(this);
    }
  }

  @Override
  public void see(Function function, Signature sig, Declaration tail) {
    writer.print("function ");
    sig.eval(this);
    writer.print(';'); nl();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(GenericType genericType, Type param, Type type) {
    writer.print('<');
    param.eval(this);
    writer.print('>');
    type.eval(this);
  }

  @Override
  public void see(HavocCmd havocCmd, AtomId id) {
    writer.print("havoc ");
    writer.print(id);
    writer.print(';'); nl();
  }

  @Override
  public void see(Identifiers identifiers, AtomId id, Identifiers tail) {
    id.eval(this);
    if (tail != null) {
      writer.print(", ");
      tail.eval(this);
    }
  }

  @Override
  public void see(Implementation implementation, Signature sig, Body body, Declaration tail) {
    writer.print("implementation ");
    sig.eval(this);
    body.eval(this);
    nl();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(Index index, Expr a, Expr b) {
    writer.print('[');
    a.eval(this);
    if (b != null) {
      writer.print(", ");
      b.eval(this);
    }
    writer.print(']');
  }

  @Override
  public void see(PrimitiveType primitiveType, PrimitiveType.Ptype ptype) {
    writer.print(typeRep.get(ptype));
  }

  @Override
  public void see(Procedure procedure, Signature sig, Specification spec, Body body, Declaration tail) {
    writer.print("procedure ");
    sig.eval(this);
    if (body == null) writer.print(';');
    if (spec != null) {
      ++indentLevel; nl();
      spec.eval(this);
      --indentLevel; nl();
    }
    if (body != null) body.eval(this);
    nl();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(Signature signature, String name, Declaration args, Declaration results) {
    ++skipVar;
    writer.print(name);
    writer.print('(');
    if (args != null) args.eval(this);
    writer.print(')');
    if (results != null) {
      writer.print(" returns (");
      results.eval(this);
      writer.print(')');
    }
    --skipVar;
  }

  @Override
  public void see(Specification specification, Specification.SpecType type, Expr expr, boolean free, Specification tail) {
    if (free) writer.print("free ");
    writer.print(specRep.get(type));
    expr.eval(this);
    writer.print(';'); nl();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(TypeDecl typeDecl, String name, Declaration tail) {
    writer.print("type ");
    writer.print(name);
    writer.print(';');
    nl();
    tail.eval(this);
  }

  @Override
  public void see(UnaryOp unaryOp, UnaryOp.Op op, Expr e) {
    writer.print(unRep.get(op));
    e.eval(this);
  }

  @Override
  public void see(UserType userType, String name) {
    writer.print(name);
  }

  @Override
  public void see(VariableDecl variableDecl, String name, Type type, Declaration tail) {
    if (skipVar==0) writer.print("var ");
    if (name != null) {
      writer.print(name);
      writer.print(" : ");
    }
    type.eval(this);
    if (skipVar>0) {
      if (tail != null) writer.print(", ");
    } else {
      writer.print(';'); nl();
    }
    if (tail != null) tail.eval(this);
  }
  
  @Override
  public void see(Trigger trigger, String label, Exprs exprs, Trigger tail) {
    writer.print('{');
    if (label != null) {
      writer.print(':');
      writer.print(label);
      writer.print(' ');
    }
    if (exprs != null) exprs.eval(this);
    writer.print("} ");
    if (tail != null) tail.eval(this);
  }

  
  /**
   * @param args
   */
  public static void main(String[] args) {
    // TODO: Tests.
  }

}
