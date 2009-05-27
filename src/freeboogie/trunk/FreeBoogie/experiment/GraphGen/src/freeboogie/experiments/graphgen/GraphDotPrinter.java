package freeboogie.experiments.graphgen;
import java.io.PrintStream;
import java.util.Collection;

public class GraphDotPrinter <T> {

  protected final PrintStream ps;

  public GraphDotPrinter(PrintStream ps) {
    this.ps = ps;
    
    ps.println("digraph {");
    ps.println();
  }

  public void printNode(Node<T> node) {
    ps.print('"');
    ps.print(node.getId());
    ps.print('"');
    ps.println(";");
  }
  
  public void printEdgesForNode(Node<T> node) {
    for (Node<T> succ : node.getSuccessors()) {
      printEdge(node, succ);
    }
  }
  
  public void printNodes(Node<T>[] nodes) {
    for (Node<T> node : nodes) {
      printNode(node); 
    }
    for (Node<T> node : nodes) {
      printEdgesForNode(node); 
    }
  }
  
  public void printNodes(Collection<Node<T>> nodes) {
    for (Node<T> node : nodes) {
      printNode(node); 
    }
    for (Node<T> node : nodes) {
      printEdgesForNode(node); 
    }
  }
  
  public void printEdge(Node<T> node1, Node<T> node2) {
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
