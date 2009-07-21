package b2bpl.bytecode;


public class ExceptionHandler {

  private final InstructionHandle start;

  private final InstructionHandle end;

  private final InstructionHandle handler;

  private final JClassType type;

  public ExceptionHandler(
      InstructionHandle start,
      InstructionHandle end,
      InstructionHandle handler,
      JClassType type) {
    this.start = start;
    this.end = end;
    this.handler = handler;
    this.type = type;
  }

  public InstructionHandle getStart() {
    return start;
  }

  public InstructionHandle getEnd() {
    return end;
  }

  public InstructionHandle getHandler() {
    return handler;
  }

  public JClassType getType() {
    return type;
  }

  public boolean isActiveFor(InstructionHandle instruction) {
    return (start.getIndex() <= instruction.getIndex())
          && (end.getIndex() >  instruction.getIndex());
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append("Exception handler - ");
    sb.append("start: " + start.getIndex());
    sb.append(", ");
    sb.append("end: " + end.getIndex());
    sb.append(", ");
    sb.append("handler: " + handler.getIndex());
    sb.append(", ");
    sb.append("type: " + type.getName());

    return sb.toString();
  }
}
