package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class LBinArithInstruction extends ArithmeticInstruction {

  private static String[] runtimeExceptions;

  public static final LBinArithInstruction LADD =
    new LBinArithInstruction(Opcodes.LADD);

  public static final LBinArithInstruction LSUB =
    new LBinArithInstruction(Opcodes.LSUB);

  public static final LBinArithInstruction LMUL =
    new LBinArithInstruction(Opcodes.LMUL);

  public static final LBinArithInstruction LDIV =
    new LBinArithInstruction(Opcodes.LDIV);

  public static final LBinArithInstruction LREM =
    new LBinArithInstruction(Opcodes.LREM);

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

  public void accept(InstructionVisitor visitor) {
    visitor.visitLBinArithInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
