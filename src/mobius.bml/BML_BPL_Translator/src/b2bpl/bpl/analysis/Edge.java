package b2bpl.bpl.analysis;

import b2bpl.graph.AbstractEdge;


/**
 * Concrete subclass of an {@code AbstractEdge} to be used in conjunction with
 * the {@link BasicBlock} class in the {@link ControlFlowGraph} of a BoogiePL
 * procedure implementation.
 *
 * @see BasicBlock
 * @see ControlFlowGraph
 *
 * @author Ovidio Mallo
 */
public class Edge extends AbstractEdge<BasicBlock, Edge> {

  /**
   * Sets the {@code source} and {@code target} basic blocks of the edge being
   * created.
   *
   * @param source  The source basic block of the edge being created.
   * @param target  The target basic block of the edge being created.
   */
  public Edge(BasicBlock source, BasicBlock target) {
    super(source, target);
  }
}
