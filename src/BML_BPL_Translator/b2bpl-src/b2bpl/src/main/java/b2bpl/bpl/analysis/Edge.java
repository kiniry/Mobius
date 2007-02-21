package b2bpl.bpl.analysis;

import b2bpl.graph.AbstractEdge;


public class Edge extends AbstractEdge<BasicBlock, Edge> {

  public Edge(BasicBlock source, BasicBlock target) {
    super(source, target);
  }
}
