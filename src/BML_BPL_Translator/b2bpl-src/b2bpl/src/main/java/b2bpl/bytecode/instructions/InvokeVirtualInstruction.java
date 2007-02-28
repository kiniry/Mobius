package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.Opcodes;


public class InvokeVirtualInstruction extends InvokeInstruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.NullPointerException"
  };

  public InvokeVirtualInstruction(
      JReferenceType methodOwner,
      String methodName,
      JType returnType,
      JType[] parameterTypes) {
    super(
        Opcodes.INVOKEVIRTUAL,
        methodOwner,
        methodName,
        returnType,
        parameterTypes);
  }

  public String[] getRuntimeExceptions() {
    return RUNTIME_EXCEPTIONS;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitInvokeVirtualInstruction(this);
  }
}
