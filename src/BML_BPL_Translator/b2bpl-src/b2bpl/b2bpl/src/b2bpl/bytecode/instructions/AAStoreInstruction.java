package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Opcodes;


public class AAStoreInstruction extends Instruction {

  private static final String[] RUNTIME_EXCEPTIONS = new String[] {
    "java.lang.NullPointerException",
    "java.lang.ArrayIndexOutOfBoundsException",
    "java.lang.ArrayStoreException"
  };

  public static final AAStoreInstruction AASTORE = new AAStoreInstruction();

  private AAStoreInstruction() {
    super(Opcodes.AASTORE);
  }

  public String[] getRuntimeExceptions() {
    return RUNTIME_EXCEPTIONS;
  }

  public void accept(InstructionVisitor visitor) {
    visitor.visitAAStoreInstruction(this);
  }

  public String toString() {
    return Opcodes.NAMES[opcode];
  }
}
