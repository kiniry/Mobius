package b2bpl.bpl.transformation;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import b2bpl.bpl.EmptyBPLVisitor;
import b2bpl.bpl.analysis.BasicBlock;
import b2bpl.bpl.analysis.CFGBuilder;
import b2bpl.bpl.analysis.ControlFlowGraph;
import b2bpl.bpl.analysis.Edge;
import b2bpl.bpl.analysis.LoopTargetDetector;
import b2bpl.bpl.ast.BPLAssertCommand;
import b2bpl.bpl.ast.BPLAssumeCommand;
import b2bpl.bpl.ast.BPLAxiom;
import b2bpl.bpl.ast.BPLBasicBlock;
import b2bpl.bpl.ast.BPLCommand;
import b2bpl.bpl.ast.BPLConstantDeclaration;
import b2bpl.bpl.ast.BPLDeclaration;
import b2bpl.bpl.ast.BPLExpression;
import b2bpl.bpl.ast.BPLFunction;
import b2bpl.bpl.ast.BPLGotoCommand;
import b2bpl.bpl.ast.BPLHavocCommand;
import b2bpl.bpl.ast.BPLImplementation;
import b2bpl.bpl.ast.BPLImplementationBody;
import b2bpl.bpl.ast.BPLProcedure;
import b2bpl.bpl.ast.BPLProgram;
import b2bpl.bpl.ast.BPLReturnCommand;
import b2bpl.bpl.ast.BPLTransferCommand;
import b2bpl.bpl.ast.BPLTypeDeclaration;
import b2bpl.bpl.ast.BPLVariableDeclaration;
import b2bpl.bpl.ast.BPLVariableExpression;


public class LoopTransformator implements BPLTransformator {

  private List<BPLDeclaration> declarations;

  public BPLProgram transform(BPLProgram program) {
    declarations = new ArrayList<BPLDeclaration>();
    Transformator transformator = new Transformator();
    program.accept(transformator);
    return new BPLProgram(
        declarations.toArray(new BPLDeclaration[declarations.size()]));
  }

  private final class Transformator extends EmptyBPLVisitor<Object> {

    private BPLImplementationBody transformLoops(BPLImplementationBody body) {
      ControlFlowGraph cfg = new CFGBuilder().build(body);
      cfg.analyze();
      List<BPLBasicBlock> blocks = new ArrayList<BPLBasicBlock>();
      Iterator<BasicBlock> cfgBlocks = cfg.blockIterator();
      while (cfgBlocks.hasNext()) {
        BasicBlock cfgBlock = cfgBlocks.next();
        if (!cfg.isSyntheticBlock(cfgBlock)) {
          blocks.add(transformBlock(cfg, cfgBlock));
        }
      }
      return new BPLImplementationBody(
          body.getVariableDeclarations(),
          blocks.toArray(new BPLBasicBlock[blocks.size()]));
    }

    private BPLBasicBlock transformBlock(
        ControlFlowGraph cfg,
        BasicBlock cfgBlock) {
      List<BPLCommand> commands = new ArrayList<BPLCommand>();

      if (cfgBlock.isBackEdgeTarget()) {
        List<BPLVariableExpression> loopTargets =
          new ArrayList<BPLVariableExpression>();
        LoopTargetDetector loopTargetDetector = new LoopTargetDetector();
        for (String name : loopTargetDetector.detect(cfg, cfgBlock)) {
          loopTargets.add(new BPLVariableExpression(name));
        }
        commands.add(new BPLHavocCommand(
            loopTargets.toArray(
                new BPLVariableExpression[loopTargets.size()])));
      }

      boolean collectInvariants = cfgBlock.isBackEdgeTarget();
      for (BPLCommand command : cfgBlock.getBPLBlock().getCommands()) {
        if (collectInvariants && (command instanceof BPLAssertCommand)) {
          BPLAssertCommand assertion = (BPLAssertCommand) command;
          commands.add(new BPLAssumeCommand(assertion.getExpression()));
        } else {
          collectInvariants &= command.isPassive();
          commands.add(command);
        }
      }

      List<String> targetLabels = new ArrayList<String>();
      Iterator<Edge> outEdges = cfgBlock.outEdgeIterator();
      while (outEdges.hasNext()) {
        Edge outEdge = outEdges.next();
        BasicBlock successor = outEdge.getTarget();
        if (!cfg.isSyntheticBlock(successor)) {
          if (successor.isBackEdgeTarget()) {
            for (BPLExpression inv : getInvariants(successor.getBPLBlock())) {
              commands.add(new BPLAssertCommand(inv));
            }
          }
          if (!outEdge.isBackEdge()) {
            targetLabels.add(successor.getBPLBlock().getLabel());
          }
        }
      }

      BPLTransferCommand transferCommand;
      if (targetLabels.size() == 0) {
        transferCommand = BPLReturnCommand.RETURN;
      } else {
        transferCommand = new BPLGotoCommand(
            targetLabels.toArray(new String[targetLabels.size()]));
      }
      return new BPLBasicBlock(
          cfgBlock.getBPLBlock().getLabel(),
          commands.toArray(new BPLCommand[commands.size()]),
          transferCommand);
    }

    private List<BPLExpression> getInvariants(BPLBasicBlock block) {
      List<BPLExpression> invariants = new ArrayList<BPLExpression>();
      for (BPLCommand command : block.getCommands()) {
        if (command instanceof BPLAssertCommand) {
          BPLAssertCommand assertion = (BPLAssertCommand) command;
          invariants.add(assertion.getExpression());
        } else if (!command.isPassive()) {
          break;
        }
      }
      return invariants;
    }

    public Object visitProgram(BPLProgram program) {
      for (BPLDeclaration declaration : program.getDeclarations()) {
        declaration.accept(this);
      }
      return null;
    }

    public Object visitAxiom(BPLAxiom axiom) {
      declarations.add(axiom);
      return null;
    }

    public Object visitConstantDeclaration(BPLConstantDeclaration declaration) {
      declarations.add(declaration);
      return null;
    }

    public Object visitImplementation(BPLImplementation implementation) {
      declarations.add(new BPLImplementation(
          implementation.getProcedureName(),
          implementation.getInParameters(),
          implementation.getOutParameters(),
          transformLoops(implementation.getBody())));
      return null;
    }

    public Object visitProcedure(BPLProcedure procedure) {
      if (procedure.getBody() == null) {
        declarations.add(procedure);
      } else {
        declarations.add(new BPLProcedure(
            procedure.getName(),
            procedure.getInParameters(),
            procedure.getOutParameters(),
            procedure.getSpecification(),
            transformLoops(procedure.getBody())));
      }
      return null;
    }

    public Object visitTypeDeclaration(BPLTypeDeclaration declaration) {
      declarations.add(declaration);
      return null;
    }

    public Object visitVariableDeclaration(BPLVariableDeclaration declaration) {
      declarations.add(declaration);
      return null;
    }

    public Object visitFunction(BPLFunction function) {
      declarations.add(function);
      return null;
    }
  }
}
