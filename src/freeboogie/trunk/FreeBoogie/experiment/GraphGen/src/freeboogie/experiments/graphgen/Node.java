package freeboogie.experiments.graphgen;
import java.util.LinkedList;
import java.util.List;


public class Node<Payload> {

  private final int id;
  
  private final List<Node<Payload>> predecessors;
  private final List<Node<Payload>> successors;
  private final Payload payload;
  
  public Node(Payload payload, Counter counter) {
    this.id = counter.getIncreasedCount();
    this.payload = payload;
    predecessors = new LinkedList<Node<Payload>>();
    successors = new LinkedList<Node<Payload>>();
  }
  
  public void addPredecessor(Node<Payload> node) {
    predecessors.add(node);
    node.successors.add(this);
  }
  
  public void addSuccessor(Node<Payload> node) {
    successors.add(node);
    node.predecessors.add(this);
  }

  public int getId() {
    return id;
  }

  public List<Node<Payload>> getPredecessors() {
    return predecessors;
  }

  public List<Node<Payload>> getSuccessors() {
    return successors;
  }
  
  public Payload getPayload() {
    return payload;
  }

  @Override
  public String toString() {
    return "" + id;
  }
  
  
  
}
