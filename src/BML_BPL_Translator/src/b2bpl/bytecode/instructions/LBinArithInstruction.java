package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class LBinArithInstruction extends ArithmeticInstruction {

  private static String[] runtimeExceptions;

  public static final LBinArithInstruction LADD =
    new LBinArithInstruction(IOpCodes.LADD);

  public static final LBinArithInstruction LSUB =
    new LBinArithInstruction(IOpCodes.LSUB);

  public static final LBinArithInstruction LMUL =
    new LBinArithInstruction(IOpCodes.LMUL);

  public static final LBinArithInstruction LDIV =
    new LBinArithInstruction(IOpCodes.LDIV);

  public static final LBinArithInstruction LREM =
    new LBinArithInstruction(IOpCodes.LREM);

  private LBinArithInstruction(int opcode) {
    super(opcode);
  }

  public String[] getRuntimeExceptions() {
    if (runtimeExceptions == null) {
      if (equals(LDIV) || equals(LREM)) {
        runtimeExceptions = new String[] { "java.lang.ArithmeticException" };
      } else {
        runtimeExceptions = new String[0];
      }
    }
    return runtimeExceptions;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitLBinArithInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
