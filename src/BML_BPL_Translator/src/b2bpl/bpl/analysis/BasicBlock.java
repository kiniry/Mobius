package b2bpl.bpl.analysis;

import b2bpl.bpl.ast.BPLBasicBlock;
import b2bpl.graph.AbstractVertex;


/**
 * Concrete subclass of an {@code AbstractVertex} to be used in conjunction with
 * the {@link Edge} class in the {@link ControlFlowGraph} of a BoogiePL
 * procedure implementation.
 *
 * <p>
 * Since a BoogiePL procedure implementation already consists of a set of
 * basic blocks as required for a control flow graph, this class is basically a
 * simple wrapper class around a {@link BPLBasicBlock}.
 * </p>
 *
 * @see Edge
 * @see ControlFlowGraph
 * @see BPLBasicBlock
 *
 * @author Ovidio Mallo
 */
public class BasicBlock extends AbstractVertex<BasicBlock, Edge> {

  /**
   * The BoogiePL basic block belonging to this basic block or {@code null} if
   * no such block exists.
   */
  private BPLBasicBlock bplBlock;

  /**
   * Constructs a new basic block in the control flow graph containing no
   * BoogiePL basic block. This constructor should only be used for the
   * synthetic entry and exit blocks created in every control flow graph.
   */
  public BasicBlock() {
    this(null);
  }

  /**
   * Constructs a new basic block in the control flow graph around the given
   * BoogiePL basic block {@code bplBlock}.
   *
   * @param bplBlock  The BoogiePL basic block belonging to the basic block
   *                  being created or {@code null} if no such block exists.
   */
  public BasicBlock(BPLBasicBlock bplBlock) {
    this.bplBlock = bplBlock;
  }

  protected Edge newPredecessorEdge(BasicBlock predecessor) {
    return new Edge(predecessor, this);
  }

  protected Edge newSuccessorEdge(BasicBlock successor) {
    return new Edge(this, successor);
  }

  /**
   * Returns the BoogiePL basic block belonging to this basic block or
   * {@code null} if no such block exists.
   *
   * @return  The BoogiePL basic block belonging to this basic block or
   *          {@code null} if no such block exists.
   */
  public BPLBasicBlock getBPLBlock() {
    return bplBlock;
  }
}
