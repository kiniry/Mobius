package b2bpl.bpl.analysis;

import java.util.HashMap;

import b2bpl.bpl.ast.BPLBasicBlock;
import b2bpl.bpl.ast.BPLImplementationBody;


/**
 * Builds up a {@link ControlFlowGraph} for a given BoogiePL procedure
 * implementation.
 *
 * @author Ovidio Mallo
 *
 * @see ControlFlowGraph
 */
public class CFGBuilder {

  /**
   * Builds up a control flow graph for the given {@code body} of a BoogiePL
   * procedure implementation.
   *
   * @param body  The body of a BoogiePL procedure implementation.
   * @return      The control flow graph for the BoogiePL procedure
   *              implementation.
   */
  public ControlFlowGraph build(BPLImplementationBody body) {
    ControlFlowGraph cfg = new ControlFlowGraph();

    // Wrap every BoogiePL block into a new basic block which is added to the
    // control flow graph being constructed. In addition, we set up a map from
    // the BoogiePL block labels to their corresponding basic blocks in the
    // control flow graph.
    HashMap<String, BasicBlock> cfgBlocks = new HashMap<String, BasicBlock>();
    for (BPLBasicBlock bplBlock : body.getBasicBlocks()) {
      BasicBlock cfgBlock = new BasicBlock(bplBlock);
      cfgBlocks.put(bplBlock.getLabel(), cfgBlock);
      cfg.addBlock(cfgBlock);
    }

    // Go through all the basic block of the control flow graph created above
    // and define their successors.
    for (BasicBlock cfgBlock : cfgBlocks.values()) {
      BPLBasicBlock bplBlock = cfgBlock.getBPLBlock();
      String[] targetLabels = bplBlock.getTransferCommand().getTargetLabels();
      if (targetLabels.length == 0) {
        // If we have no successors, we add an edge to the synthetic exit block
        // of the control flow graph.
        cfgBlock.addSuccessor(cfg.getExitBlock());
      } else {
        for (String succLabel : targetLabels) {
          // Look up the successor basic block for the given BoogiePL block
          // label and add it to the successors of the current basic block.
          BasicBlock succCFGBlock = cfgBlocks.get(succLabel);
          cfgBlock.addSuccessor(succCFGBlock);
        }
      }
    }

    return cfg;
  }
}
