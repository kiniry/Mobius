package freeboogie.experiments.graphgen;

import java.io.PrintStream;

public class FlowGraphDotPrinter extends GraphDotPrinter<FlowGraphPayload> {

  public FlowGraphDotPrinter(PrintStream ps) {
    super(ps);
  }

  @Override
  public void printNode(Node<FlowGraphPayload> node) {
    FlowGraphPayload payload = node.getPayload();
    
    ps.print('"');
    ps.print(node.getId());
    ps.print('"');
    
    ps.print(" [label=\"");
    ps.print(node.getId());
    ps.print(" R:");
    ps.print(payload.isRead() ? "T" : "F");
    ps.print(",W:");
    ps.print(payload.isWrite() ? "T" : "F");
    ps.print("\"]");
    
    ps.println(";");
  }
  
  
  
}
