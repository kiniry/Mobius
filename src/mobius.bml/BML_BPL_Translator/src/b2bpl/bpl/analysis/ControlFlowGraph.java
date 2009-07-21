package b2bpl.bpl.analysis;

import b2bpl.graph.AbstractFlowGraph;


/**
 * Concrete subclass of an {@code AbstractFlowGraph} to be used as the control
 * flow graph of BoogiePL procedure implementations. The basic blocks and edges
 * of the control flow graph are represented by the {@link BasicBlock} and
 * {@link Edge} classes, respectively.
 *
 * @author Ovidio Mallo
 *
 * @see BasicBlock
 * @see Edge
 */
public class ControlFlowGraph extends AbstractFlowGraph<BasicBlock, Edge> {

  protected BasicBlock newBlock() {
    return new BasicBlock();
  }
}
