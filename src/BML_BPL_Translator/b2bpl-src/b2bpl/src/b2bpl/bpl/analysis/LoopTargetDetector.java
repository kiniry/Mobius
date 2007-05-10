package b2bpl.bpl.analysis;

import java.util.HashSet;
import java.util.Iterator;

import b2bpl.bpl.EmptyBPLVisitor;
import b2bpl.bpl.ast.BPLArrayExpression;
import b2bpl.bpl.ast.BPLAssignmentCommand;
import b2bpl.bpl.ast.BPLBasicBlock;
import b2bpl.bpl.ast.BPLCallCommand;
import b2bpl.bpl.ast.BPLCommand;
import b2bpl.bpl.ast.BPLHavocCommand;
import b2bpl.bpl.ast.BPLOldExpression;
import b2bpl.bpl.ast.BPLVariableExpression;


/**
 * Detects the set of loop targets of all the loops starting at a given loop
 * header block of a control flow graph.
 *
 * @author Ovidio Mallo
 */
public class LoopTargetDetector {

  /**
   * Returns the set of loop targets of all the loops starting at the given
   * {@code loopHeader}.
   *
   * @param cfg         The control flow graph to which the given
   *                    {@code loopHeader} belongs.
   * @param loopHeader  The loop header block for which to compute the set of
   *                    loop targets.
   * @return            The set of loop targets of all the loops starting at
   *                    the given {@code loopHeader}.
   */
  public HashSet<String> detect(ControlFlowGraph cfg, BasicBlock loopHeader) {
    // The blocks of all loops starting at the given loopHeader.
    HashSet<BasicBlock> loopBlocks = new HashSet<BasicBlock>();

    // Go through all the back edges whose target is the given loopHeader and
    // add the blocks of their natural loops to our set of loop blocks.
    Iterator<Edge> edges = loopHeader.inEdgeIterator();
    while (edges.hasNext()) {
      Edge edge = edges.next();
      if (edge.isBackEdge()) {
        loopBlocks.addAll(cfg.computeNaturalLoop(edge));
      }
    }

    // Search for the loop targets in all the loop blocks accumulated above.
    Detector detector = new Detector();
    for (BasicBlock loopBlock : loopBlocks) {
      loopBlock.getBPLBlock().accept(detector);
    }

    return detector.loopTargets;
  }

  /**
   * The visitor performing the actual loop target detection inside BoogiePL
   * blocks.
   *
   * <p>
   * Loop targets are always {@code BPLVariableExpression}s appearing in the
   * BoogiePL AST, which show up in one of the following contexts:
   * <ul>
   *   <li>As the target of a <tt>havoc</tt> command.</li>
   *   <li>On the left hand side of an assignment command.</li>
   *   <li>As the result variables of a procedure call command.</li>
   * </ul>
   * Therefore, this class only visits those parts of the AST and whenever a
   * {@code BPLVariableExpression} is encountered, it is guaranteed to be a loop
   * target.
   * </p>
   *
   * @author Ovidio Mallo
   */
  private final class Detector extends EmptyBPLVisitor<Object> {

    /** The set of loop targets detected so far. */
    private final HashSet<String> loopTargets = new HashSet<String>();

    public Object visitBasicBlock(BPLBasicBlock block) {
      for (BPLCommand command : block.getCommands()) {
        command.accept(this);
      }
      return null;
    }

    public Object visitAssignmentCommand(BPLAssignmentCommand command) {
      // For an assignment expression, we only need to visit the assignment's
      // left hand side as it is the one containing the loop target.
      command.getLeft().accept(this);
      return null;
    }

    public Object visitCallCommand(BPLCallCommand command) {
      // All the result variable expressions of a procedure call command are
      // loop targets, but we nevertheless visit the variable expressions to
      // handle their occurrence at a central point and to more cleanly follow
      // the visitor pattern.
      for (BPLVariableExpression variable : command.getResultVariables()) {
        variable.accept(this);
      }
      return null;
    }

    public Object visitHavocCommand(BPLHavocCommand command) {
      // All the variable expressions inside a havoc command are loop targets,
      // but we nevertheless visit the variable expressions to handle their
      // occurrence at a central point and to more cleanly follow the visitor
      // pattern.
      for (BPLVariableExpression variable : command.getVariables()) {
        variable.accept(this);
      }
      return null;
    }

    public Object visitArrayExpression(BPLArrayExpression expr) {
      // For an array expression, we only need to visit the prefix expression as
      // it is the one containing the loop target.
      expr.getPrefix().accept(this);
      return null;
    }

    public Object visitOldExpression(BPLOldExpression expr) {
      expr.getExpression().accept(this);
      return null;
    }

    public Object visitVariableExpression(BPLVariableExpression expr) {
      // Every variable expression reached by this visitor is guaranteed to be
      // a loop target.
      loopTargets.add(expr.getIdentifier());
      return null;
    }
  }
}
