package mobius.bico;

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


public class BranchInstructionVisitor extends EmptyVisitor {
  /** the result string. */
  private String fRes;

  private BranchInstructionVisitor() {
    
  }
  
  @Override
  public void visitGotoInstruction(final GotoInstruction ins) {
    final String index = Util.printZ(ins.getIndex());
    fRes = "Goto " + index;
  }

  @Override
  public void visitIFEQ(final IFEQ ins) {
    fRes = "If0 EqInt " + Util.printZ(ins.getIndex());
  }
  
  @Override
  public void visitIFGE(final IFGE ins) {
    fRes = "If0 GeInt " + Util.printZ(ins.getIndex());
  }

  @Override
  public void visitIFGT(final IFGT ins) {
    fRes = "If0 GtInt " + Util.printZ(ins.getIndex());
  }

  @Override
  public void visitIFLE(final IFLE ins) {
    fRes = "If0 LeInt " + Util.printZ(ins.getIndex());
  }

  @Override
  public void visitIFLT(final IFLT ins) {
    fRes = "If0 LtInt " + Util.printZ(ins.getIndex());
  }
  
  @Override
  public void visitIFNE(final IFNE ins) {
    fRes = "If0 NeInt " + Util.printZ(ins.getIndex());
  }
  
  @Override
  public void visitIFNONNULL(final IFNONNULL ins) {
    fRes = "Ifnull NeRef " + Util.printZ(ins.getIndex());
  }
  
  @Override
  public void visitIFNULL(final IFNULL ins) {
    fRes = "Ifnull EqRef " + Util.printZ(ins.getIndex());
  }
  
  @Override
  public void visitIF_ACMPEQ(final IF_ACMPEQ ins) {
    fRes = "If_acmp EqRef " + Util.printZ(ins.getIndex());

  }
  
  @Override
  public void visitIF_ACMPNE(final IF_ACMPNE ins) {
    fRes = "If_acmp NeRef " + Util.printZ(ins.getIndex());
  }

  @Override
  public void visitIF_ICMPEQ(final IF_ICMPEQ ins) {
    fRes = "If_icmp EqInt " + Util.printZ(ins.getIndex());
  }

  @Override
  public void visitIF_ICMPGE(final IF_ICMPGE ins) {
    fRes = "If_icmp GeInt " + Util.printZ(ins.getIndex());
  }
  
  @Override
  public void visitIF_ICMPGT(final IF_ICMPGT ins) {
    fRes = "If_icmp GtInt " + Util.printZ(ins.getIndex());
  }
  
  @Override
  public void visitIF_ICMPLE(final IF_ICMPLE ins) {
    fRes = "If_icmp LeInt " + Util.printZ(ins.getIndex());
  }
  
  @Override
  public void visitIF_ICMPLT(final IF_ICMPLT ins) {
    fRes = "If_icmp LtInt " + Util.printZ(ins.getIndex());
  }
  
  @Override
  public void visitIF_ICMPNE(final IF_ICMPNE ins) {
    fRes = "If_icmp NeInt " + Util.printZ(ins.getIndex());
  }


  @Override
  public void visitJsrInstruction(final JsrInstruction ins) {
    fRes = Util.unhandled("JsrInstruction", ins);
  }
  
  @Override
  public void visitSelect(final Select ins) {
    fRes = Util.unimplemented("Select", ins);
  }


  public static String translate(BranchInstruction ins) {
    final BranchInstructionVisitor v = new BranchInstructionVisitor();
    ins.accept(v);
    if (v.fRes.equals("")) {
      v.fRes = Util.unknown("BranchInstruction", ins);
    }
    return v.fRes;
  }


}
