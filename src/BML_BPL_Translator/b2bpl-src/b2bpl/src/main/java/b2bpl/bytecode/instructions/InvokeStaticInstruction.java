package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.Opcodes;


public class InvokeStaticInstruction extends InvokeInstruction {

  public InvokeStaticInstruction(
      JReferenceType methodOwner,
      String methodName,
      JType returnType,
      JType[] parameterTypes) {
    super(
        Opcodes.INVOKESTATIC,
        methodOwner,
        methodName,
        returnType,
        parameterTypes);
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitInvokeStaticInstruction(this);
  }
}
