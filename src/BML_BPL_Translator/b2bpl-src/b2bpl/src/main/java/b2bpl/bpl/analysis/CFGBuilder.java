package b2bpl.bpl.analysis;

import java.util.HashMap;

import b2bpl.bpl.ast.BPLBasicBlock;
import b2bpl.bpl.ast.BPLImplementationBody;
import b2bpl.bpl.ast.BPLReturnCommand;


public class CFGBuilder {

  public ControlFlowGraph build(BPLImplementationBody body) {
    ControlFlowGraph cfg = new ControlFlowGraph();

    HashMap<String, BasicBlock> cfgBlocks = new HashMap<String, BasicBlock>();
    for (BPLBasicBlock bplBlock : body.getBasicBlocks()) {
      BasicBlock cfgBlock = new BasicBlock(bplBlock);
      cfgBlocks.put(bplBlock.getLabel(), cfgBlock);
      cfg.addBlock(cfgBlock);
    }

    for (BasicBlock cfgBlock : cfgBlocks.values()) {
      BPLBasicBlock bplBlock = cfgBlock.getBPLBlock();
      for (String succLabel : bplBlock.getTransferCommand().getTargetLabels()) {
        BasicBlock succCFGBlock = cfgBlocks.get(succLabel);
        cfgBlock.addSuccessor(succCFGBlock);
      }
      if (bplBlock.getTransferCommand() instanceof BPLReturnCommand) {
        cfgBlock.addSuccessor(cfg.getExitBlock());
      }
    }

    return cfg;
  }
}
