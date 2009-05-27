package freeboogie.experiments.graphgen;

public class Graph<T> {

  private final Node<T> startNode;
  private final Node<T> endNode;
  
  public Graph(Node<T> startNode, Node<T> endNode) {
    super();
    this.startNode = startNode;
    this.endNode = endNode;
  }

  public Node<T> getStartNode() {
    return startNode;
  }

  public Node<T> getEndNode() {
    return endNode;
  }
  
  public Graph<T> join(Graph<T> graph) {
    return new Graph<T>(this.startNode, graph.endNode);
  }
  
  @Deprecated
  public static <T> Graph<T> join(Graph<T> graph1, Graph<T> graph2) {
    graph1.endNode.addSuccessor(graph2.startNode);
    return graph1.join(graph2);
  }

  @Override
  public String toString() {
    return "Graph with start: " + startNode + " and end: " + endNode;
  }
  
}
