package b2bpl.bytecode.analysis;

import java.util.Iterator;

import b2bpl.bytecode.InstructionHandle;
import b2bpl.graph.AbstractVertex;


public class BasicBlock extends AbstractVertex<BasicBlock, Edge> {

  private InstructionHandle firstInstruction;

  private InstructionHandle lastInstruction;

  protected Edge newPredecessorEdge(BasicBlock predecessor) {
    return new Edge(predecessor, this);
  }

  protected Edge newSuccessorEdge(BasicBlock successor) {
    return new Edge(this, successor);
  }

  public InstructionHandle getFirstInstruction() {
    return firstInstruction;
  }

  public InstructionHandle getLastInstruction() {
    return lastInstruction;
  }

  public void setInstructions(
      InstructionHandle firstInstruction,
      InstructionHandle lastInstruction) {
    this.firstInstruction = firstInstruction;
    this.lastInstruction = lastInstruction;
  }

  public Iterator<InstructionHandle> instructionIterator() {
    return new InstructionIterator(firstInstruction, lastInstruction);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append("block_" + getID() + ":");
    sb.append(System.getProperty("line.separator"));

    if (firstInstruction != null) {
      InstructionHandle instruction = firstInstruction;
      while (instruction != lastInstruction.getNext()) {
        sb.append("  ");
        sb.append(instruction);
        sb.append(System.getProperty("line.separator"));
        instruction = instruction.getNext();
      }
    }

    sb.append("  Successors: ");
    for (int i = 0; i < outEdges.size(); i++) {
      if (i > 0) {
        sb.append(", ");
      }
      Edge outEdge = outEdges.get(i);
      BasicBlock successor = outEdge.getTarget();
      sb.append("block_" + successor.getID());
      if (outEdge.isBackEdge()) {
        sb.append("(*)");
      }
    }
    sb.append(System.getProperty("line.separator"));

    return sb.toString();
  }

  private static final class InstructionIterator
      implements Iterator<InstructionHandle> {

    private InstructionHandle current;

    private final InstructionHandle last;

    public InstructionIterator(
        InstructionHandle first, 
        InstructionHandle last) {
      this.current = first;
      this.last = last;
    }

    public boolean hasNext() {
      return current != null;
    }

    public InstructionHandle next() {
      InstructionHandle next = current;
      current = (next == last) ? null : current.getNext();
      return next;
    }

    public void remove() {
      throw new UnsupportedOperationException();
    }
  }
}
