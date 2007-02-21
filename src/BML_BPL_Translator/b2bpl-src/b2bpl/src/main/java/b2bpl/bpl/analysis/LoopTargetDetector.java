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


public class LoopTargetDetector {

  public HashSet<String> detect(ControlFlowGraph cfg, BasicBlock loopHeader) {
    HashSet<BasicBlock> loopBlocks = new HashSet<BasicBlock>();
    Iterator<Edge> edges = loopHeader.inEdgeIterator();
    while (edges.hasNext()) {
      Edge edge = edges.next();
      if (edge.isBackEdge()) {
        loopBlocks.addAll(cfg.computeNaturalLoop(edge));
      }
    }

    Detector detector = new Detector();
    for (BasicBlock loopBlock : loopBlocks) {
      loopBlock.getBPLBlock().accept(detector);
    }

    return detector.loopTargets;
  }

  private final class Detector extends EmptyBPLVisitor<Object> {

    private final HashSet<String> loopTargets = new HashSet<String>();

    public Object visitBasicBlock(BPLBasicBlock block) {
      for (BPLCommand command : block.getCommands()) {
        command.accept(this);
      }
      block.getTransferCommand().accept(this);
      return null;
    }

    public Object visitAssignmentCommand(BPLAssignmentCommand command) {
      command.getLeft().accept(this);
      return null;
    }

    public Object visitCallCommand(BPLCallCommand command) {
      for (BPLVariableExpression variable : command.getResultVariables()) {
        variable.accept(this);
      }
      return null;
    }

    public Object visitHavocCommand(BPLHavocCommand command) {
      for (BPLVariableExpression variable : command.getVariables()) {
        variable.accept(this);
      }
      return null;
    }

    public Object visitArrayExpression(BPLArrayExpression expr) {
      expr.getPrefix().accept(this);
      return null;
    }

    public Object visitOldExpression(BPLOldExpression expr) {
      expr.getExpression().accept(this);
      return null;
    }

    public Object visitVariableExpression(BPLVariableExpression expr) {
      loopTargets.add(expr.getIdentifier());
      return null;
    }
  }
}
