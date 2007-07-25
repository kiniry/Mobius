package b2bpl.bytecode;


public class UnsupportedInstructionException extends RuntimeException {

  private static final long serialVersionUID = -3952540367225723149L;

  private final int opcode;

  public UnsupportedInstructionException(int opcode) {
    this(opcode, "Unsupported instruction: " + IOpCodes.NAMES[opcode]);
  }

  public UnsupportedInstructionException(int opcode, String message) {
    super(message);
    this.opcode = opcode;
  }

  public int getOpcode() {
    return opcode;
  }
}
