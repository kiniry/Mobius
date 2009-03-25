package freeboogie.experiments.graphgen;
import java.io.PrintStream;
import java.util.List;



public class GraphDotPrinter {

  private final PrintStream ps;

  public GraphDotPrinter(PrintStream ps, int numberOfNodes) {
    this.ps = ps;
    
    ps.println("digraph {");
    ps.println();
  }

  public void printNode(Node<?> node) {
    ps.print('"');
    ps.print(node.getId());
    ps.print('"');
    ps.println(";");
  }
  
  public void printEdgesForNode(Node<?> node) {
    for (Node<?> succ : node.getSuccessors()) {
      printEdge(node, succ);
    }
  }
  
  public <T> void printNodes(Node<T>[] nodes) {
    for (Node<T> node : nodes) {
      printNode(node); 
    }
    for (Node<T> node : nodes) {
      printEdgesForNode(node); 
    }
  }
  
  public <T> void printNodes(List<Node<T>> nodes) {
    for (Node<T> node : nodes) {
      printNode(node); 
    }
    for (Node<T> node : nodes) {
      printEdgesForNode(node); 
    }
  }
  
  public void printEdge(Node<?> node1, Node<?> node2) {
    ps.print('"');
    ps.print(node1.getId());
    ps.print('"');
    ps.print(" -> ");
    ps.print('"');
    ps.print(node2.getId());
    ps.print('"');
    ps.println(';');
  }
  
  public void finish() {
    ps.println();
    ps.println("}");
    ps.close();
  }
  
}
