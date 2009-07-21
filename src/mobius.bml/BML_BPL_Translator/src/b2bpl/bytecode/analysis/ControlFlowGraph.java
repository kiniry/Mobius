package b2bpl.bytecode.analysis;

import b2bpl.bytecode.InstructionHandle;
import b2bpl.graph.AbstractFlowGraph;


/**
 * Concrete subclass of an {@code AbstractFlowGraph} to be used as the control
 * flow graph of bytecode methods. The basic blocks and edges of the control
 * flow graph are represented by the {@link BasicBlock} and {@link Edge}
 * classes, respectively.
 *
 * <p>
 * This specialization of an {@code AbstractFlowGraph} provides methods specific
 * to bytecode methods such a the possibility to retrieve the basic block leaded
 * by a given bytecode instruction.
 * </p>
 *
 * <p>
 * An important design decision in the implementation of this control flow graph
 * for bytecode methods is the fact that no special information is attached
 * to the edges of the graph such as whether they represent a conditional or
 * unconditional branch, or whether an edge represents an exception being
 * thrown. This implies that if this kind of information is somehow required,
 * one must extract it from the bytecode instruction giving rise to the edges
 * in the flow graph. The advantage of the here adopted approach, on the other
 * hand, is that no redundant information already contained in the individual
 * bytecode instructions is attached to the edges of the control flow graph. In
 * addition, if one really wants to have all the information attached to the
 * graph's edges in order to avoid having to look at the instructions, the kind
 * of information an edge must store may get very inhomogeneous. As an example,
 * one may want to know to which case label a specific successor of a switch
 * instruction belongs while for a method invocation instruction it is important
 * to know whether it has a successor representing an exception handler and, if
 * so, which exceptions that exception handler catches. Attaching information
 * to the individual edges which is that different by its very nature may thus
 * easily get messy.
 * </p>
 *
 * @see BasicBlock
 * @see Edge
 *
 * @author Ovidio Mallo
 */
public class ControlFlowGraph extends AbstractFlowGraph<BasicBlock, Edge> {

  protected BasicBlock newBlock() {
    return new BasicBlock();
  }

  /**
   * Returns the basic block of this control flow graph leaded by the given
   * {@code instruction} or {@code null} if no such block exists.
   *
   * @param instruction  The eventual leader of the basic block to retrieve.
   * @return             The basic block of this control flow graph leaded by
   *                     the given {@code instruction} or {@code null} if no
   *                     such block exists.
   */
  public BasicBlock findBlockStartingAt(InstructionHandle instruction) {
    for (BasicBlock block : blocks) {
      if (block.getFirstInstruction() == instruction) {
        return block;
      }
    }
    return null;
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    for (BasicBlock block : blocks) {
      sb.append(block);
      sb.append(System.getProperty("line.separator"));
    }

    return sb.toString();
  }
}
