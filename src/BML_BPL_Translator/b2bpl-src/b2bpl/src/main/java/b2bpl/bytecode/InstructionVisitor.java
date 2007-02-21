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
import b2bpl.bytecode.instructions.VALoadInstruction;
import b2bpl.bytecode.instructions.VAStoreInstruction;
import b2bpl.bytecode.instructions.IBinArithInstruction;
import b2bpl.bytecode.instructions.IBitwiseInstruction;
import b2bpl.bytecode.instructions.IConstantInstruction;
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
import b2bpl.bytecode.instructions.VCastInstruction;


public interface InstructionVisitor {

  void visitNopInstruction(NopInstruction insn);

  void visitILoadInstruction(ILoadInstruction insn);

  void visitALoadInstruction(ALoadInstruction insn);

  void visitIStoreInstruction(IStoreInstruction insn);

  void visitAStoreInstruction(AStoreInstruction insn);

  void visitIConstantInstruction(IConstantInstruction insn);

  void visitLdcInstruction(LdcInstruction insn);

  void visitAConstNullInstruction(AConstNullInstruction insn);

  void visitGetFieldInstruction(GetFieldInstruction insn);

  void visitPutFieldInstruction(PutFieldInstruction insn);

  void visitGetStaticInstruction(GetStaticInstruction insn);

  void visitPutStaticInstruction(PutStaticInstruction insn);

  void visitVALoadInstruction(VALoadInstruction insn);

  void visitAALoadInstruction(AALoadInstruction insn);

  void visitVAStoreInstruction(VAStoreInstruction insn);

  void visitAAStoreInstruction(AAStoreInstruction insn);

  void visitArrayLengthInstruction(ArrayLengthInstruction insn);

  void visitInvokeVirtualInstruction(InvokeVirtualInstruction insn);

  void visitInvokeStaticInstruction(InvokeStaticInstruction insn);

  void visitInvokeSpecialInstruction(InvokeSpecialInstruction insn);

  void visitInvokeInterfaceInstruction(InvokeInterfaceInstruction insn);

  void visitIBinArithInstruction(IBinArithInstruction insn);

  void visitIBitwiseInstruction(IBitwiseInstruction insn);

  void visitINegInstruction(INegInstruction insn);

  void visitIIncInstruction(IIncInstruction insn);

  void visitIfICmpInstruction(IfICmpInstruction insn);

  void visitIfACmpInstruction(IfACmpInstruction insn);

  void visitIfInstruction(IfInstruction insn);

  void visitIfNonNullInstruction(IfNonNullInstruction insn);

  void visitIfNullInstruction(IfNullInstruction insn);

  void visitGotoInstruction(GotoInstruction insn);

  void visitLookupSwitchInstruction(LookupSwitchInstruction insn);

  void visitTableSwitchInstruction(TableSwitchInstruction insn);

  void visitReturnInstruction(ReturnInstruction insn);

  void visitIReturnInstruction(IReturnInstruction insn);

  void visitAReturnInstruction(AReturnInstruction insn);

  void visitAThrowInstruction(AThrowInstruction insn);

  void visitNewInstruction(NewInstruction insn);

  void visitNewArrayInstruction(NewArrayInstruction insn);

  void visitANewArrayInstruction(ANewArrayInstruction insn);

  void visitMultiANewArrayInstruction(MultiANewArrayInstruction insn);

  void visitCheckCastInstruction(CheckCastInstruction insn);

  void visitVCastInstruction(VCastInstruction insn);

  void visitInstanceOfInstruction(InstanceOfInstruction insn);

  void visitPopInstruction(PopInstruction insn);

  void visitPop2Instruction(Pop2Instruction insn);

  void visitSwapInstruction(SwapInstruction insn);

  void visitDupInstruction(DupInstruction insn);

  void visitDup2Instruction(Dup2Instruction insn);

  void visitDupX1Instruction(DupX1Instruction insn);

  void visitDupX2Instruction(DupX2Instruction insn);

  void visitDup2X1Instruction(Dup2X1Instruction insn);

  void visitDup2X2Instruction(Dup2X2Instruction insn);
}
