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

/**
 * Translate the Array instructions to bicolano friendly versions.
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class ArrayInstructionVisitor extends EmptyVisitor {
  /** the result string. */
  private String fRes;

  /**
   * Does nothing.
   */
  private ArrayInstructionVisitor() {
    fRes = "";
  }
  
  /**
   * Set the result to <code>Vaload Aarray</code>.
   * @param obj ignored
   */
  @Override
  public void visitAALOAD(final AALOAD obj) {
    fRes = "Vaload Aarray";
  }
  
  /**
   * Set the result to <code>Vastore Aarray</code>.
   * @param obj ignored
   */
  @Override
  public void visitAASTORE(final AASTORE obj) {
    fRes = "Vastore Aarray";
  }
  
  /**
   * Set the result to <code>Vaload Barray</code>.
   * @param obj ignored
   */
  @Override
  public void visitBALOAD(final BALOAD obj) {
    fRes = "Vaload Barray";
  }
  
  /**
   * Set the result to <code>Vastore Barray</code>.
   * @param obj ignored
   */
  @Override
  public void visitBASTORE(final BASTORE obj) {
    fRes = "Vastore Barray";
  }
  
  
  /**
   * Unhandled instruction.
   * @param obj ignored
   */
  @Override
  public void visitCALOAD(final CALOAD obj) {
    fRes = Util.unhandled("ArrayInstruction", obj);
  }
  
  /**
   * Unhandled instruction.
   * @param obj ignored
   */
  @Override
  public void visitCASTORE(final CASTORE obj) {
    fRes = Util.unhandled("ArrayInstruction", obj);
  }
  
  
  /**
   * Unhandled instruction.
   * @param obj ignored
   */
  @Override
  public void visitDALOAD(final DALOAD obj) {
    fRes = Util.unhandled("ArrayInstruction", obj);
  }
  
  
  /**
   * Unhandled instruction.
   * @param obj ignored
   */
  @Override
  public void visitDASTORE(final DASTORE obj) {
    fRes = Util.unhandled("ArrayInstruction", obj);
  }
  
  
  /**
   * Unhandled instruction.
   * @param obj ignored
   */
  @Override
  public void visitFALOAD(final FALOAD obj) {
    fRes = Util.unhandled("ArrayInstruction", obj);
  }
  
  
  /**
   * Unhandled instruction.
   * @param obj ignored
   */
  @Override
  public void visitFASTORE(final FASTORE obj) {
    fRes = Util.unhandled("ArrayInstruction", obj);
  }
  
  /**
   * Set the result to <code>Vaload Iarray</code>.
   * @param obj ignored
   */
  @Override
  public void visitIALOAD(final IALOAD obj) {
    fRes = "Vaload Iarray";
  }
  
  /**
   * Set the result to <code>Vastore Iarray</code>.
   * @param obj ignored
   */
  @Override
  public void visitIASTORE(final IASTORE obj) {
    fRes = "Vastore Iarray";
  }
  

  /**
   * Unhandled instruction.
   * @param obj ignored
   */
  @Override
  public void visitLALOAD(final LALOAD obj) {
    fRes = Util.unhandled("ArrayInstruction", obj);
  }
  
  /**
   * Unhandled instruction.
   * @param obj ignored
   */
  @Override
  public void visitLASTORE(final LASTORE obj) {
    fRes = Util.unhandled("ArrayInstruction", obj);
  }
  
  /**
   * Set the result to <code>Vaload Sarray</code>.
   * @param obj ignored
   */
  @Override
  public void visitSALOAD(final SALOAD obj) {
    fRes = "Vaload Sarray";
  }
  
  /**
   * Set the result to <code>Vastore Sarray</code>.
   * @param obj ignored
   */
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
      v.fRes = Util.unknown("ArrayInstruction", ins);
    }
    return v.fRes;
  }
}
