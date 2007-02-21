package b2bpl.bpl.analysis;

import b2bpl.graph.AbstractFlowGraph;


public class ControlFlowGraph extends AbstractFlowGraph<BasicBlock, Edge> {

  protected BasicBlock newBlock() {
    return new BasicBlock();
  }
}
