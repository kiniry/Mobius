package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionHandle;
import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class LookupSwitchInstruction extends SwitchInstruction {

  private final InstructionHandle defaultTarget;

  private final int[] keys;

  private final InstructionHandle[] targets;

  public LookupSwitchInstruction(
      InstructionHandle defaultTarget,
      int[] keys,
      InstructionHandle[] targets) {
    super(IOpCodes.LOOKUPSWITCH);
    this.defaultTarget = defaultTarget;
    this.keys = keys;
    this.targets = targets;
  }

  public InstructionHandle getDefaultTarget() {
    return defaultTarget;
  }

  public int[] getKeys() {
    return keys;
  }

  public InstructionHandle[] getTargets() {
    return targets;
  }

  public boolean isUnconditionalBranch() {
    return true;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitLookupSwitchInstruction(this);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append(IOpCodes.NAMES[opcode]);
    sb.append(System.getProperty("line.separator"));
    for (int i = 0; i < targets.length; i++) {
      sb.append("        case ");
      sb.append(keys[i]).append(": ").append(targets[i].getIndex());
      sb.append(System.getProperty("line.separator"));
    }
    sb.append("        default: ").append(defaultTarget.getIndex());

    return sb.toString();
  }
}
