package b2bpl.bytecode.analysis;

import b2bpl.bytecode.InstructionHandle;
import b2bpl.graph.AbstractFlowGraph;


public class ControlFlowGraph extends AbstractFlowGraph<BasicBlock, Edge> {

  protected BasicBlock newBlock() {
    return new BasicBlock();
  }

  public BasicBlock findBlockStartingAt(InstructionHandle instruction) {
    for (BasicBlock block : blocks) {
      if (block.getFirstInstruction() == instruction) {
        return block;
      }
    }
    return null;
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    for (BasicBlock block : blocks) {
      sb.append(block);
      sb.append(System.getProperty("line.separator"));
    }

    return sb.toString();
  }
}
