package b2bpl.bytecode;

import b2bpl.bytecode.instructions.AALoadInstruction;
import b2bpl.bytecode.instructions.AAStoreInstruction;
import b2bpl.bytecode.instructions.AConstNullInstruction;
import b2bpl.bytecode.instructions.ALoadInstruction;
import b2bpl.bytecode.instructions.ANewArrayInstruction;
import b2bpl.bytecode.instructions.AReturnInstruction;
import b2bpl.bytecode.instructions.AStoreInstruction;
import b2bpl.bytecode.instructions.AThrowInstruction;
import b2bpl.bytecode.instructions.ArrayLengthInstruction;
import b2bpl.bytecode.instructions.CheckCastInstruction;
import b2bpl.bytecode.instructions.Dup2Instruction;
import b2bpl.bytecode.instructions.Dup2X1Instruction;
import b2bpl.bytecode.instructions.Dup2X2Instruction;
import b2bpl.bytecode.instructions.DupInstruction;
import b2bpl.bytecode.instructions.DupX1Instruction;
import b2bpl.bytecode.instructions.DupX2Instruction;
import b2bpl.bytecode.instructions.GetFieldInstruction;
import b2bpl.bytecode.instructions.GetStaticInstruction;
import b2bpl.bytecode.instructions.GotoInstruction;
import b2bpl.bytecode.instructions.IBinArithInstruction;
import b2bpl.bytecode.instructions.IBitwiseInstruction;
import b2bpl.bytecode.instructions.IIncInstruction;
import b2bpl.bytecode.instructions.ILoadInstruction;
import b2bpl.bytecode.instructions.INegInstruction;
import b2bpl.bytecode.instructions.IReturnInstruction;
import b2bpl.bytecode.instructions.IStoreInstruction;
import b2bpl.bytecode.instructions.IfACmpInstruction;
import b2bpl.bytecode.instructions.IfICmpInstruction;
import b2bpl.bytecode.instructions.IfInstruction;
import b2bpl.bytecode.instructions.IfNonNullInstruction;
import b2bpl.bytecode.instructions.IfNullInstruction;
import b2bpl.bytecode.instructions.InstanceOfInstruction;
import b2bpl.bytecode.instructions.InvokeInterfaceInstruction;
import b2bpl.bytecode.instructions.InvokeSpecialInstruction;
import b2bpl.bytecode.instructions.InvokeStaticInstruction;
import b2bpl.bytecode.instructions.InvokeVirtualInstruction;
import b2bpl.bytecode.instructions.LBinArithInstruction;
import b2bpl.bytecode.instructions.LBitwiseInstruction;
import b2bpl.bytecode.instructions.LCmpInstruction;
import b2bpl.bytecode.instructions.LLoadInstruction;
import b2bpl.bytecode.instructions.LNegInstruction;
import b2bpl.bytecode.instructions.LReturnInstruction;
import b2bpl.bytecode.instructions.LStoreInstruction;
import b2bpl.bytecode.instructions.LdcInstruction;
import b2bpl.bytecode.instructions.LookupSwitchInstruction;
import b2bpl.bytecode.instructions.MultiANewArrayInstruction;
import b2bpl.bytecode.instructions.NewArrayInstruction;
import b2bpl.bytecode.instructions.NewInstruction;
import b2bpl.bytecode.instructions.NopInstruction;
import b2bpl.bytecode.instructions.Pop2Instruction;
import b2bpl.bytecode.instructions.PopInstruction;
import b2bpl.bytecode.instructions.PutFieldInstruction;
import b2bpl.bytecode.instructions.PutStaticInstruction;
import b2bpl.bytecode.instructions.ReturnInstruction;
import b2bpl.bytecode.instructions.SwapInstruction;
import b2bpl.bytecode.instructions.TableSwitchInstruction;
import b2bpl.bytecode.instructions.VALoadInstruction;
import b2bpl.bytecode.instructions.VAStoreInstruction;
import b2bpl.bytecode.instructions.VCastInstruction;
import b2bpl.bytecode.instructions.VConstantInstruction;


public class EmptyInstructionVisitor implements InstructionVisitor {

  public void visitNopInstruction(NopInstruction insn) {
    // do nothing
  }

  public void visitILoadInstruction(ILoadInstruction insn) {
    // do nothing
  }

  public void visitLLoadInstruction(LLoadInstruction insn) {
    // do nothing
  }

  public void visitALoadInstruction(ALoadInstruction insn) {
    // do nothing
  }

  public void visitIStoreInstruction(IStoreInstruction insn) {
    // do nothing
  }

  public void visitLStoreInstruction(LStoreInstruction insn) {
    // do nothing
  }

  public void visitAStoreInstruction(AStoreInstruction insn) {
    // do nothing
  }

  public void visitVConstantInstruction(VConstantInstruction insn) {
    // do nothing
  }

  public void visitLdcInstruction(LdcInstruction insn) {
    // do nothing
  }

  public void visitAConstNullInstruction(AConstNullInstruction insn) {
    // do nothing
  }

  public void visitGetFieldInstruction(GetFieldInstruction insn) {
    // do nothing
  }

  public void visitPutFieldInstruction(PutFieldInstruction insn) {
    // do nothing
  }

  public void visitGetStaticInstruction(GetStaticInstruction insn) {
    // do nothing
  }

  public void visitPutStaticInstruction(PutStaticInstruction insn) {
    // do nothing
  }

  public void visitVALoadInstruction(VALoadInstruction insn) {
    // do nothing
  }

  public void visitAALoadInstruction(AALoadInstruction insn) {
    // do nothing
  }

  public void visitVAStoreInstruction(VAStoreInstruction insn) {
    // do nothing
  }

  public void visitAAStoreInstruction(AAStoreInstruction insn) {
    // do nothing
  }

  public void visitArrayLengthInstruction(ArrayLengthInstruction insn) {
    // do nothing
  }

  public void visitInvokeVirtualInstruction(InvokeVirtualInstruction insn) {
    // do nothing
  }

  public void visitInvokeStaticInstruction(InvokeStaticInstruction insn) {
    // do nothing
  }

  public void visitInvokeSpecialInstruction(InvokeSpecialInstruction insn) {
    // do nothing
  }

  public void visitInvokeInterfaceInstruction(InvokeInterfaceInstruction insn) {
    // do nothing
  }

  public void visitIBinArithInstruction(IBinArithInstruction insn) {
    // do nothing
  }

  public void visitLBinArithInstruction(LBinArithInstruction insn) {
    // do nothing
  }

  public void visitIBitwiseInstruction(IBitwiseInstruction insn) {
    // do nothing
  }

  public void visitLBitwiseInstruction(LBitwiseInstruction insn) {
    // do nothing
  }

  public void visitINegInstruction(INegInstruction insn) {
    // do nothing
  }

  public void visitLNegInstruction(LNegInstruction insn) {
    // do nothing
  }

  public void visitIIncInstruction(IIncInstruction insn) {
    // do nothing
  }

  public void visitIfICmpInstruction(IfICmpInstruction insn) {
    // do nothing
  }

  public void visitIfACmpInstruction(IfACmpInstruction insn) {
    // do nothing
  }

  public void visitIfInstruction(IfInstruction insn) {
    // do nothing
  }

  public void visitIfNonNullInstruction(IfNonNullInstruction insn) {
    // do nothing
  }

  public void visitIfNullInstruction(IfNullInstruction insn) {
    // do nothing
  }

  public void visitLCmpInstruction(LCmpInstruction insn) {
    // do nothing
  }

  public void visitGotoInstruction(GotoInstruction insn) {
    // do nothing
  }

  public void visitLookupSwitchInstruction(LookupSwitchInstruction insn) {
    // do nothing
  }

  public void visitTableSwitchInstruction(TableSwitchInstruction insn) {
    // do nothing
  }

  public void visitReturnInstruction(ReturnInstruction insn) {
    // do nothing
  }

  public void visitIReturnInstruction(IReturnInstruction insn) {
    // do nothing
  }

  public void visitLReturnInstruction(LReturnInstruction insn) {
    // do nothing
  }

  public void visitAReturnInstruction(AReturnInstruction insn) {
    // do nothing
  }

  public void visitAThrowInstruction(AThrowInstruction insn) {
    // do nothing
  }

  public void visitNewInstruction(NewInstruction insn) {
    // do nothing
  }

  public void visitNewArrayInstruction(NewArrayInstruction insn) {
    // do nothing
  }

  public void visitANewArrayInstruction(ANewArrayInstruction insn) {
    // do nothing
  }

  public void visitMultiANewArrayInstruction(MultiANewArrayInstruction insn) {
    // do nothing
  }

  public void visitCheckCastInstruction(CheckCastInstruction insn) {
    // do nothing
  }

  public void visitVCastInstruction(VCastInstruction insn) {
    // do nothing
  }

  public void visitInstanceOfInstruction(InstanceOfInstruction insn) {
    // do nothing
  }

  public void visitPopInstruction(PopInstruction insn) {
    // do nothing
  }

  public void visitPop2Instruction(Pop2Instruction insn) {
    // do nothing
  }

  public void visitSwapInstruction(SwapInstruction insn) {
    // do nothing
  }

  public void visitDupInstruction(DupInstruction insn) {
    // do nothing
  }

  public void visitDup2Instruction(Dup2Instruction insn) {
    // do nothing
  }

  public void visitDupX1Instruction(DupX1Instruction insn) {
    // do nothing
  }

  public void visitDupX2Instruction(DupX2Instruction insn) {
    // do nothing
  }

  public void visitDup2X1Instruction(Dup2X1Instruction insn) {
    // do nothing
  }

  public void visitDup2X2Instruction(Dup2X2Instruction insn) {
    // do nothing
  }
}
