package b2bpl.bytecode.instructions;

import b2bpl.bytecode.InstructionHandle;
import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;


public class TableSwitchInstruction extends SwitchInstruction {

  private final int minIndex;

  private final int maxIndex;

  private final InstructionHandle defaultTarget;

  private final InstructionHandle[] targets;

  public TableSwitchInstruction(
      int minIndex,
      int maxIndex,
      InstructionHandle defaultTarget,
      InstructionHandle[] targets) {
    super(IOpCodes.TABLESWITCH);
    this.minIndex = minIndex;
    this.maxIndex = maxIndex;
    this.defaultTarget = defaultTarget;
    this.targets = targets;
  }

  public int getMinIndex() {
    return minIndex;
  }

  public int getMaxIndex() {
    return maxIndex;
  }

  public InstructionHandle getDefaultTarget() {
    return defaultTarget;
  }

  public InstructionHandle[] getTargets() {
    return targets;
  }

  public boolean isUnconditionalBranch() {
    return true;
  }

  public void accept(IInstructionVisitor visitor) {
    visitor.visitTableSwitchInstruction(this);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append(IOpCodes.NAMES[opcode]);
    sb.append(" [").append(minIndex).append(", ").append(maxIndex).append("]");
    sb.append(System.getProperty("line.separator"));
    for (int i = 0; i < targets.length; i++) {
      sb.append("        case ");
      sb.append(minIndex + i).append(": ").append(targets[i].getIndex());
      sb.append(System.getProperty("line.separator"));
    }
    sb.append("        default: ").append(defaultTarget.getIndex());

    return sb.toString();
  }
}
