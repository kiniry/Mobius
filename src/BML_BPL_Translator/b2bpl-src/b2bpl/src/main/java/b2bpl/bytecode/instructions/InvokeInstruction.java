package b2bpl.bytecode.instructions;

import b2bpl.bytecode.BCMethod;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.Opcodes;


public abstract class InvokeInstruction extends Instruction {

  protected final JReferenceType methodOwner;

  protected final String methodName;

  protected final JType methodReturnType;

  protected final JType[] methodParameterTypes;

  protected final String methodDescriptor;

  protected BCMethod method;

  public InvokeInstruction(
      int opcode,
      JReferenceType methodOwner,
      String methodName,
      JType returnType,
      JType[] parameterTypes) {
    super(opcode);
    this.methodOwner = methodOwner;
    this.methodName = methodName;
    this.methodReturnType = returnType;
    this.methodParameterTypes = parameterTypes;
    this.methodDescriptor =
      JType.computeMethodDescriptor(returnType, parameterTypes);
  }

  public JReferenceType getMethodOwner() {
    return methodOwner;
  }

  public String getMethodName() {
    return methodName;
  }

  public JType getMethodReturnType() {
    return methodReturnType;
  }

  public JType[] getMethodParameterTypes() {
    return methodParameterTypes;
  }

  public String getMethodDescriptor() {
    return methodDescriptor;
  }

  public BCMethod getMethod() {
    return method;
  }

  public void setMethod(BCMethod method) {
    this.method = method;
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append(Opcodes.NAMES[opcode]);
    sb.append(' ');
    sb.append(methodOwner.getName());
    sb.append('.');
    sb.append(methodName);
    sb.append(" : ");
    sb.append('(');
    for (int i = 0; i < methodParameterTypes.length; i++) {
      if (i > 0) {
        sb.append(", ");
      }
      sb.append(methodParameterTypes[i].getName());
    }
    sb.append(')');
    sb.append(methodReturnType.getName());

    return sb.toString();
  }
}
