package freeboogie.experiments.graphgen;

import java.io.PrintStream;
import java.util.Collection;
import java.util.List;

public class GraphBoogiePrinter {

  private static final String NAME_PREFIX = "node";
  private static final String VAR_NAME = "x";
  
  private final PrintStream ps;

  public GraphBoogiePrinter(PrintStream ps) {
    this.ps = ps;
    
    ps.println("procedure main() {");
    ps.print("  var ");
    ps.print(VAR_NAME);
    ps.println(" : int;");
    ps.println("  var dummy : int;");
    ps.println();
  }
  
  
  public GraphBoogiePrinter print(Collection<Node<FlowGraphPayload>> list) {
    for (Node<FlowGraphPayload> node : list) {
      print(node);
    }
    return this;
  }
  
  private void print(Node<FlowGraphPayload> node) {
    if (node.getSuccessors().size() == 0) {
      printTerminalNode(node);
    } else {
      printNormalNode(node);
    }
  }
    
  private void printTerminalNode(Node<FlowGraphPayload> node) {
    ps.print(nodeName(node));
    ps.println(":");
    ps.println("  return;");
    ps.println();
  }
  
  private void printNormalNode(Node<FlowGraphPayload> node) {
    ps.print(nodeName(node));
    ps.println(":");
    node.getPayload().printBoogie(ps);
    ps.print("  goto ");
    
    List<Node<FlowGraphPayload>> succList = node.getSuccessorsAsList();
    
    if (node.getSuccessors().size() == 1) {
      ps.print(nodeName(succList.get(0)));
      ps.println(";");
    } else if (succList.size() == 2) {
      ps.print(nodeName(succList.get(0)));
      ps.print(", ");
      ps.print(nodeName(succList.get(1)));
      ps.println(";");
    } else {
      System.out.println("Warning, more than 2 successors for this node (" + node.toString() + ")");
    }
    ps.println();
  }
  
  private String nodeName(Node<?> node) {
    return NAME_PREFIX + node.getId();
  }
  
  public void finish() {
    ps.print("}");
    ps.close();
  }
  
  public static void printBoogie(PrintStream ps, Collection<Node<FlowGraphPayload>> nodes) {
    new GraphBoogiePrinter(ps).print(nodes).finish();
  }
  
}
