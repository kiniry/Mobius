package b2bpl.bytecode;


public class TroublePosition {

  private JClassType classType;

  private BCMethod method;

  private InstructionHandle instruction;

  public TroublePosition(BCMethod method, InstructionHandle instruction) {
    this(method.getOwner(), method, instruction);
  }

  public TroublePosition(
      JClassType classType,
      BCMethod method,
      InstructionHandle instruction) {
    this.classType = classType;
    this.method = method;
    this.instruction = instruction;
  }

  public JClassType getClassType() {
    return classType;
  }

  public void setClassType(JClassType classType) {
    this.classType = classType;
  }

  public BCMethod getMethod() {
    return method;
  }

  public void setMethod(BCMethod method) {
    this.method = method;
  }

  public InstructionHandle getInstruction() {
    return instruction;
  }

  public void setInstruction(InstructionHandle instruction) {
    this.instruction = instruction;
  }
}
