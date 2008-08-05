package mobius.bico.visitors;

import mobius.bico.Util;
import mobius.bico.bicolano.coq.Translator;

import org.apache.bcel.generic.BranchInstruction;
import org.apache.bcel.generic.EmptyVisitor;
import org.apache.bcel.generic.GotoInstruction;
import org.apache.bcel.generic.IFEQ;
import org.apache.bcel.generic.IFGE;
import org.apache.bcel.generic.IFGT;
import org.apache.bcel.generic.IFLE;
import org.apache.bcel.generic.IFLT;
import org.apache.bcel.generic.IFNE;
import org.apache.bcel.generic.IFNONNULL;
import org.apache.bcel.generic.IFNULL;
import org.apache.bcel.generic.IF_ACMPEQ;
import org.apache.bcel.generic.IF_ACMPNE;
import org.apache.bcel.generic.IF_ICMPEQ;
import org.apache.bcel.generic.IF_ICMPGE;
import org.apache.bcel.generic.IF_ICMPGT;
import org.apache.bcel.generic.IF_ICMPLE;
import org.apache.bcel.generic.IF_ICMPLT;
import org.apache.bcel.generic.IF_ICMPNE;
import org.apache.bcel.generic.JsrInstruction;
import org.apache.bcel.generic.Select;

/**
 * Translate the Branch instructions to bicolano friendly versions.
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class BranchInstructionVisitor extends EmptyVisitor {
  /** the result string. */
  private String fRes;

  /**
   * Does nothing.
   */
  private BranchInstructionVisitor() {
    fRes = "";
  }
  
  /**
   * Set the result to <code>Goto index</code>.
   * @param ins the instruction from where to get the index
   * of the jump
   */
  @Override
  public void visitGotoInstruction(final GotoInstruction ins) {
    final String index = Translator.toZ(ins.getIndex());
    fRes = "Goto " + index;
  }

  
  /**
   * Set the result to <code>If0 EqInt index</code>.
   * @param ins the instruction from where to get the index
   * of the jump
   */
  @Override
  public void visitIFEQ(final IFEQ ins) {
    fRes = "If0 EqInt " + Translator.toZ(ins.getIndex());
  }
  
  /**
   * Set the result to <code>If0 GeInt index</code>.
   * @param ins the instruction from where to get the index
   * of the jump
   */
  @Override
  public void visitIFGE(final IFGE ins) {
    fRes = "If0 GeInt " + Translator.toZ(ins.getIndex());
  }

  /**
   * Set the result to <code>If0 GtInt index</code>.
   * @param ins the instruction from where to get the index
   * of the jump
   */
  @Override
  public void visitIFGT(final IFGT ins) {
    fRes = "If0 GtInt " + Translator.toZ(ins.getIndex());
  }

  /**
   * Set the result to <code>If0 LeInt index</code>.
   * @param ins the instruction from where to get the index
   * of the jump
   */
  @Override
  public void visitIFLE(final IFLE ins) {
    fRes = "If0 LeInt " + Translator.toZ(ins.getIndex());
  }

  /**
   * Set the result to <code>If0 LtInt index</code>.
   * @param ins the instruction from where to get the index
   * of the jump
   */
  @Override
  public void visitIFLT(final IFLT ins) {
    fRes = "If0 LtInt " + Translator.toZ(ins.getIndex());
  }
  
  /**
   * Set the result to <code>If0 NeInt index</code>.
   * @param ins the instruction from where to get the index
   * of the jump
   */
  @Override
  public void visitIFNE(final IFNE ins) {
    fRes = "If0 NeInt " + Translator.toZ(ins.getIndex());
  }
  
  /**
   * Set the result to <code>Ifnull NeRef index</code>.
   * @param ins the instruction from where to get the index
   * of the jump
   */
  @Override
  public void visitIFNONNULL(final IFNONNULL ins) {
    fRes = "Ifnull NeRef " + Translator.toZ(ins.getIndex());
  }
  
  /**
   * Set the result to <code>Ifnull EqRef index</code>.
   * @param ins the instruction from where to get the index
   * of the jump
   */
  @Override
  public void visitIFNULL(final IFNULL ins) {
    fRes = "Ifnull EqRef " + Translator.toZ(ins.getIndex());
  }
  
  /**
   * Set the result to <code>Ifacmp EqRef index</code>.
   * @param ins the instruction from where to get the index
   * of the jump
   */
  @Override
  public void visitIF_ACMPEQ(final IF_ACMPEQ ins) {
    fRes = "If_acmp EqRef " + Translator.toZ(ins.getIndex());

  }
  
  /**
   * Set the result to <code>Ifacmp NeRef index</code>.
   * @param ins the instruction from where to get the index
   * of the jump
   */
  @Override
  public void visitIF_ACMPNE(final IF_ACMPNE ins) {
    fRes = "If_acmp NeRef " + Translator.toZ(ins.getIndex());
  }

  
  /**
   * Set the result to <code>Ificmp EqInt index</code>.
   * @param ins the instruction from where to get the index
   * of the jump
   */
  @Override
  public void visitIF_ICMPEQ(final IF_ICMPEQ ins) {
    fRes = "If_icmp EqInt " + Translator.toZ(ins.getIndex());
  }
  
  /**
   * Set the result to <code>Ificmp GeInt index</code>.
   * @param ins the instruction from where to get the index
   * of the jump
   */
  @Override
  public void visitIF_ICMPGE(final IF_ICMPGE ins) {
    fRes = "If_icmp GeInt " + Translator.toZ(ins.getIndex());
  }
  
  
  /**
   * Set the result to <code>Ificmp GtInt index</code>.
   * @param ins the instruction from where to get the index
   * of the jump
   */
  @Override
  public void visitIF_ICMPGT(final IF_ICMPGT ins) {
    fRes = "If_icmp GtInt " + Translator.toZ(ins.getIndex());
  }
  
  /**
   * Set the result to <code>Ificmp LeInt index</code>.
   * @param ins the instruction from where to get the index
   * of the jump
   */
  @Override
  public void visitIF_ICMPLE(final IF_ICMPLE ins) {
    fRes = "If_icmp LeInt " + Translator.toZ(ins.getIndex());
  }
  
  /**
   * Set the result to <code>Ificmp LtInt index</code>.
   * @param ins the instruction from where to get the index
   * of the jump
   */
  @Override
  public void visitIF_ICMPLT(final IF_ICMPLT ins) {
    fRes = "If_icmp LtInt " + Translator.toZ(ins.getIndex());
  }
  
  /**
   * Set the result to <code>Ificmp NeInt index</code>.
   * @param ins the instruction from where to get the index
   * of the jump
   */
  @Override
  public void visitIF_ICMPNE(final IF_ICMPNE ins) {
    fRes = "If_icmp NeInt " + Translator.toZ(ins.getIndex());
  }
  
  /**
   * Unhandled instruction.
   * @param ins ignored
   */
  @Override
  public void visitJsrInstruction(final JsrInstruction ins) {
    fRes = Util.unhandled("JsrInstruction", ins);
  }
  
  /**
   * Unhandled instruction.
   * @param ins ignored
   */
  @Override
  public void visitSelect(final Select ins) {
    fRes = Util.unimplemented("Select", ins);
  }


  /**
   * Translate the given instruction to a Bicolano version of it.
   * @param ins the instruction to translate
   * @return the bicolano compatible translation
   */
  public static String translate(final BranchInstruction ins) {
    final BranchInstructionVisitor v = new BranchInstructionVisitor();
    ins.accept(v);
    if (v.fRes.equals("")) {
      v.fRes = Util.unknown("BranchInstruction", ins);
    }
    return v.fRes;
  }


}
