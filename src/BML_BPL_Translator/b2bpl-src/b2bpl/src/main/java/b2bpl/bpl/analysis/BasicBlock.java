package b2bpl.bpl.analysis;

import b2bpl.bpl.ast.BPLBasicBlock;
import b2bpl.graph.AbstractVertex;


public class BasicBlock extends AbstractVertex<BasicBlock, Edge> {

  private BPLBasicBlock bplBlock;

  public BasicBlock() {
    this(null);
  }

  public BasicBlock(BPLBasicBlock bplBlock) {
    this.bplBlock = bplBlock;
  }

  protected Edge newPredecessorEdge(BasicBlock predecessor) {
    return new Edge(predecessor, this);
  }

  protected Edge newSuccessorEdge(BasicBlock successor) {
    return new Edge(this, successor);
  }

  public BPLBasicBlock getBPLBlock() {
    return bplBlock;
  }

  public void setBPLBlock(BPLBasicBlock bplBlock) {
    this.bplBlock = bplBlock;
  }
}
