package mobius.bico.visitors;

import mobius.bico.Util;

import org.apache.bcel.generic.AALOAD;
import org.apache.bcel.generic.AASTORE;
import org.apache.bcel.generic.ArrayInstruction;
import org.apache.bcel.generic.BALOAD;
import org.apache.bcel.generic.BASTORE;
import org.apache.bcel.generic.CALOAD;
import org.apache.bcel.generic.CASTORE;
import org.apache.bcel.generic.DALOAD;
import org.apache.bcel.generic.DASTORE;
import org.apache.bcel.generic.EmptyVisitor;
import org.apache.bcel.generic.FALOAD;
import org.apache.bcel.generic.FASTORE;
import org.apache.bcel.generic.IALOAD;
import org.apache.bcel.generic.IASTORE;
import org.apache.bcel.generic.LALOAD;
import org.apache.bcel.generic.LASTORE;
import org.apache.bcel.generic.SALOAD;
import org.apache.bcel.generic.SASTORE;

public class ArrayInstructionVisitor extends EmptyVisitor {
  /** the result string. */
  private String fRes;
  

  /**
   * Does nothing.
   */
  private ArrayInstructionVisitor() {
    fRes = "";
  }
  
  
  @Override
  public void visitAALOAD(final AALOAD obj) {
    fRes = "Vaload Aarray";
  }
  
  @Override
  public void visitAASTORE(final AASTORE obj) {
    fRes = "Vastore Aarray";
  }
  
  @Override
  public void visitBALOAD(final BALOAD obj) {
    fRes = "Vaload Barray";
  }
  
  @Override
  public void visitBASTORE(final BASTORE obj) {
    fRes = "Vastore Barray";
  }
  
  @Override
  public void visitCALOAD(final CALOAD obj) {
    fRes = Util.unhandled("ArrayInstruction", obj);
  }
  
  @Override
  public void visitCASTORE(final CASTORE obj) {
    fRes = Util.unhandled("ArrayInstruction", obj);
  }
  
  @Override
  public void visitDALOAD(final DALOAD obj) {
    fRes = Util.unhandled("ArrayInstruction", obj);
  }
  
  @Override
  public void visitDASTORE(final DASTORE obj) {
    fRes = Util.unhandled("ArrayInstruction", obj);
  }
  
  @Override
  public void visitFALOAD(final FALOAD obj) {
    fRes = Util.unhandled("ArrayInstruction", obj);
  }
  
  @Override
  public void visitFASTORE(final FASTORE obj) {
    fRes = Util.unhandled("ArrayInstruction", obj);
  }
  
  @Override
  public void visitIALOAD(final IALOAD obj) {
    fRes = "Vaload Iarray";
  }
  
  @Override
  public void visitIASTORE(final IASTORE obj) {
    fRes = "Vastore Iarray";
  }
  @Override
  public void visitLALOAD(final LALOAD obj) {
    fRes = Util.unhandled("ArrayInstruction", obj);
  }
  
  @Override
  public void visitLASTORE(final LASTORE obj) {
    fRes = Util.unhandled("ArrayInstruction", obj);
  }
  
  
  @Override
  public void visitSALOAD(final SALOAD obj) {
    fRes = "Vaload Sarray";
  }
  
  @Override
  public void visitSASTORE(final SASTORE obj) {
    fRes = "Vastore Sarray";
  }

  /**
   * Translate the given instruction to a Bicolano version of it.
   * @param ins the instruction to translate
   * @return the bicolano compatible translation
   */
  public static String translate(final ArrayInstruction ins) {
    final ArrayInstructionVisitor v = new ArrayInstructionVisitor();
    ins.accept(v);
    if (v.fRes.equals("")) {
      v.fRes = Util.unknown("BranchInstruction", ins);
    }
    return v.fRes;
  }
}
