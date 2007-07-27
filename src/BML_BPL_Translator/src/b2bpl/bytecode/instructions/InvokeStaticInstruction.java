package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.IOpCodes;


public class InvokeStaticInstruction extends InvokeInstruction {

  public InvokeStaticInstruction(
      JReferenceType methodOwner,
      String methodName,
      JType returnType,
      JType[] parameterTypes) {
    super(
        IOpCodes.INVOKESTATIC,
        methodOwner,
        methodName,
        returnType,
        parameterTypes);
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitInvokeStaticInstruction(this);
  }
}
