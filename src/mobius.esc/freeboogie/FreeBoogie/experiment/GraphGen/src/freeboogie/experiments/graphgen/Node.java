package freeboogie.experiments.graphgen;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;


public class Node<Payload> {

  private int id;
  
  private final Collection<Node<Payload>> predecessors;
  private final Collection<Node<Payload>> successors;
  private final Payload payload;
  
  public Node(Payload payload, Counter counter) {
    this.id = counter.getUnique();
    counter.increaseCount();
    this.payload = payload;
    predecessors = new LinkedHashSet<Node<Payload>>();
    successors = new LinkedHashSet<Node<Payload>>();
  }
  
  public void addPredecessor(Node<Payload> node) {
    predecessors.add(node);
    node.successors.add(this);
  }
  
  public void addSuccessor(Node<Payload> node) {
    successors.add(node);
    node.predecessors.add(this);
  }
  
  public void removePredecessor(Node<Payload> node) {
    predecessors.remove(node);
    node.successors.remove(this);
  }
  
  public void removeSuccessor(Node<Payload> node) {
    successors.remove(node);
    node.predecessors.remove(this);
  }

  public int getId() {
    return id;
  }

  public void setId(int id) {
    this.id = id;
  }

  public Collection<Node<Payload>> getPredecessors() {
    return predecessors;
  }

  public Collection<Node<Payload>> getSuccessors() {
    return successors;
  }
  
  public List<Node<Payload>> getPredecessorsAsList() {
    return new ArrayList<Node<Payload>>(predecessors);
  }

  public List<Node<Payload>> getSuccessorsAsList() {
    return new ArrayList<Node<Payload>>(successors);
  }
  
  public Payload getPayload() {
    return payload;
  }

  @Override
  public String toString() {
    return "" + id;
  }
  
  public Node<Payload> join(Node<Payload> node, Counter counter, Collection<Node<Payload>> allNodes) {
    if (node == this) {
      System.out.println("The same!");
      return this;
    }
    for (Node<Payload> succ : node.getSuccessors()) {
      this.addSuccessor(succ);
      succ.predecessors.remove(node);
    }
    for (Node<Payload> pred : node.getPredecessors()) {
      this.addPredecessor(pred);
      pred.successors.remove(node);
    }
    counter.decreaseCount();
    allNodes.remove(node);
    return this;
  }

  @SuppressWarnings("unchecked")
  @Override
  public boolean equals(Object obj) {
    if (obj instanceof Node) {
      return getId() == ((Node<Payload>)obj).getId();
    } else {
      return false;
    }
  }

  @Override
  public int hashCode() {
    return getId();
  }
  
  
  
}
