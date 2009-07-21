package b2bpl.bytecode.instructions;

import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class AAStoreInstruction extends Instruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.NullPointerException",
    "java.lang.ArrayIndexOutOfBoundsException",
    "java.lang.ArrayStoreException"
  };

  public static final AAStoreInstruction AASTORE = new AAStoreInstruction();

  private AAStoreInstruction() {
    super(IOpCodes.AASTORE);
  }

  public String[] getRuntimeExceptions() {
    return RUNTIME_EXCEPTIONS;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitAAStoreInstruction(this);
  }

  public String toString() {
    return IOpCodes.NAMES[opcode];
  }
}
