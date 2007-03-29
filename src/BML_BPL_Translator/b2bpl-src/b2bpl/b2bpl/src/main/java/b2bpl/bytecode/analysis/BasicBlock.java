package b2bpl.bytecode.analysis;

import java.util.Iterator;

import b2bpl.bytecode.InstructionHandle;
import b2bpl.graph.AbstractVertex;


/**
 * Concrete subclass of an {@code AbstractVertex} to be used in conjunction with
 * the {@link Edge} class in the {@link ControlFlowGraph} of a bytecode method.
 *
 * <p>
 * This specialization of an {@code AbstractVertex} provides methods specific to
 * bytecode methods such a the possibility to set the bytecode instructions of
 * the basic block.
 * </p>
 *
 * @see Edge
 * @see ControlFlowGraph
 *
 * @author Ovidio Mallo
 */
public class BasicBlock extends AbstractVertex<BasicBlock, Edge> {

  /**
   * The first bytecode instruction of this basic block or {@code null} if no
   * such instruction has been set.
   */
  private InstructionHandle firstInstruction;

  /**
   * The last bytecode instruction of this basic block or {@code null} if no
   * such instruction has been set.
   */
  private InstructionHandle lastInstruction;

  protected Edge newPredecessorEdge(BasicBlock predecessor) {
    return new Edge(predecessor, this);
  }

  protected Edge newSuccessorEdge(BasicBlock successor) {
    return new Edge(this, successor);
  }

  /**
   * Returns the first bytecode instruction of this basic block or {@code null}
   * if no such instruction has been set.
   *
   * @return  The first bytecode instruction of this basic block or {@code null}
   *          if no such instruction has been set.
   *
   * @see #setInstructions(InstructionHandle, InstructionHandle)
   */
  public InstructionHandle getFirstInstruction() {
    return firstInstruction;
  }

  /**
   * Returns the last bytecode instruction of this basic block or {@code null}
   * if no such instruction has been set.
   *
   * @return  The last bytecode instruction of this basic block or {@code null}
   *          if no such instruction has been set.
   *
   * @see #setInstructions(InstructionHandle, InstructionHandle)
   */
  public InstructionHandle getLastInstruction() {
    return lastInstruction;
  }

  /**
   * Sets the first and last bytecode instructions of this basic block.
   * Note that {@code lastInstruction} should be a successor of
   * {@code firstInstruction}.
   *
   * @param firstInstruction  The first bytecode instruction of this basic
   *                          block.
   * @param lastInstruction   The last bytecode instruction of this basic block.
   */
  public void setInstructions(
      InstructionHandle firstInstruction,
      InstructionHandle lastInstruction) {
    this.firstInstruction = firstInstruction;
    this.lastInstruction = lastInstruction;
  }

  /**
   * Returns an iterator for the bytecode instructions of this basic block.
   *
   * @return  An iterator for the bytecode instructions of this basic block.
   */
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

  /**
   * Simple iterator for the bytecode instructions of this basic block. Uses the
   * linked list maintained by the {@link b2bpl.bytecode.Instructions} class in
   * order to get the successor of an instruction.
   *
   * @author Ovidio Mallo
   */
  private static final class InstructionIterator
      implements Iterator<InstructionHandle> {

    /**
     * The current instruction in the basic block to be returned by the iterator
     * or {@code null} if no more instructions are available.
     */
    private InstructionHandle current;

    /**
     * The last instruction in the basic block to be returned by the iterator.
     */
    private final InstructionHandle last;

    /**
     * Initializes the {@code current} and {@code last} instructions of the
     * iterator.
     *
     * @param first  The first bytecode instruction of the basic block.
     * @param last   The last bytecode instruction of the basic block.
     */
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
      // Check whether we are returning the last instruction of the basic block.
      current = (next == last) ? null : current.getNext();
      return next;
    }

    public void remove() {
      throw new UnsupportedOperationException();
    }
  }
}
