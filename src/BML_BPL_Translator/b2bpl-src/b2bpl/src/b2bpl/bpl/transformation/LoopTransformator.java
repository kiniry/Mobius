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


/**
 * Performs a transformation on loops in the procedure implementations of a
 * given BoogiePL program which allows for a sound verification of loops.
 *
 * <p>
 * During static program verification, loops must be removed before generating
 * the verification condition which is passed to the theorem prover. This class
 * performs a set of transformations on every loop encountered in the given
 * BoogiePL program and then removes the loops. The employed transformation of
 * loops thereby guarantees that the soundness of the verification is preserved.
 * In addition, the resulting BoogiePL program is guaranteed to be loop-free
 * as long as the control flow graph of every procedure implementation in the
 * input program is <i>reducible</i>.
 * </p>
 *
 * <p>
 * The core idea of the employed loop transformation is to remove all the back
 * edges in the control flow graph of a procedure's implementation while letting
 * the loop body represent an arbitrary iteration of the loop. This is achieved
 * by applying the following set of transformations to every loop in the
 * procedure implementations of the input BoogiePL program:
 * <ul>
 *   <li>
 *     All the variables modified inside the loop (the so-called <i>loop
 *     targets</i>) are <tt>havoc</tt>'ed at the beginning of the loop header
 *     basic block in order to ensure that their values are representative for
 *     the values they might hold at any arbitrary iteration of the loop.
 *   </li>
 *   <li>
 *     The set of loop invariants are extracted from the input BoogiePL program
 *     where the expressions of all the <tt>assert</tt> commands appearing
 *     within a prefix of <i>passive</i> BoogiePL commands in the loop header's
 *     basic block are considered to be loop invariants.
 *   </li>
 *   <li>
 *     While all the loop targets need to be <tt>havoc</tt>'ed as described
 *     above in order to preserve the soundness of the verification, this leads
 *     to the problem that loop invariants depending on the value of any such
 *     loop target could not be verified after havoc'ing the variables' values.
 *     Therefore, asserting the loop invariants is pushed to the end of every
 *     immediate <i>predecessor</i> of the loop header block which, in turn,
 *     justifies that the loop invariants can now be <i>assumed</i> at the loop
 *     header block itself, right after having havoc'ed the loop targets.
 *   </li>
 *   <li>
 *     All the back edges of the control flow graph are removed which in turn
 *     ensures that the resulting procedure implementation is loop-free (as we
 *     are assuming a <i>reducible</i> control flow graph for every procedure
 *     implementation of the input BoogiePL program).
 *   </li>
 * </ul>
 * </p>
 *
 * @see BPLCommand#isPassive()
 *
 * @author Ovidio Mallo
 */
public class LoopTransformator implements BPLTransformator {

  /** The set of declarations of the new, transformed BoogiePL program. */
  private List<BPLDeclaration> declarations;

  public BPLProgram transform(BPLProgram program) {
    declarations = new ArrayList<BPLDeclaration>();
    program.accept(new Transformator());
    return new BPLProgram(
        declarations.toArray(new BPLDeclaration[declarations.size()]));
  }

  /**
   * The visitor performing the actual loop transformation in the BoogiePL
   * program.
   *
   * @author Ovidio Mallo
   */
  private final class Transformator extends EmptyBPLVisitor<Object> {

    /**
     * Transforms all the loops in the given BoogiePL implementation
     * {@code body} and returns a new implementation body resulting from this
     * transformation.
     *
     * @param body  The BoogiePL implementation body whose loops should be
     *              transformed.
     * @return      A new implementation body resulting from the transformation.
     */
    private BPLImplementationBody transformLoops(BPLImplementationBody body) {
      // For locating and transforming the loops, we first need to build up
      // the implementation's control flow graph and analyze it.
      ControlFlowGraph cfg = new CFGBuilder().build(body);
      cfg.analyze();

      // Transform every BoogiePL basic block individually and collect the
      // transformed blocks to pass them to the new, transformed implementation
      // body.
      List<BPLBasicBlock> blocks = new ArrayList<BPLBasicBlock>();
      Iterator<BasicBlock> cfgBlocks = cfg.blockIterator();
      while (cfgBlocks.hasNext()) {
        BasicBlock cfgBlock = cfgBlocks.next();
        // Make sure we skip the synthetic entry and exit blocks.
        if (!cfg.isSyntheticBlock(cfgBlock)) {
          blocks.add(transformBlock(cfg, cfgBlock));
        }
      }

      // Construct the new implementation body.
      return new BPLImplementationBody(
          body.getVariableDeclarations(),
          blocks.toArray(new BPLBasicBlock[blocks.size()]));
    }

    /**
     * Transforms the BoogiePL basic block contained in the given
     * {@code cfgBlock}. The concrete set of transformations applied to every
     * basic block depends on some of its properties and is defined as follows:
     * <ul>
     *   <li>
     *     If the given {@code cfgBlock} is a loop header block, a
     *     <tt>havoc</tt> command is inserted at the beginning of the block for
     *     all the loop targets of all the loops starting at the given
     *     {@code cfgBlock}.
     *   </li>
     *   <li>
     *     If the given {@code cfgBlock} is a loop header block, the assertions
     *     of the individual loop-invariants are turned into assumptions.
     *   </li>
     *   <li>
     *     For every successor of the given {@code cfgBlock}, if that successor
     *     is a loop header block, we assert its loop invariants at the end of
     *     the BoogiePL basic block.
     *   </li>
     *   <li>
     *     All the back edges originating from the given {@code cfgBlock} are
     *     removed.
     *   </li>
     * </ul>
     *
     * @param cfg       The control flow graph of the current implementation
     *                  body.
     * @param cfgBlock  The basic block of the control flow graph containing the
     *                  BoogiePL basic block to transform.
     * @return          A new BoogiePL basic block resulting from the
     *                  transformation.
     */
    private BPLBasicBlock transformBlock(
        ControlFlowGraph cfg,
        BasicBlock cfgBlock) {
      // Prepare a list for accumulating the commands of the new BoogiePL basic
      // block.
      List<BPLCommand> commands = new ArrayList<BPLCommand>();

      // If the basic block is a loop header, we must havoc the loop targets
      // of all the loops starting at this block.
      if (cfgBlock.isBackEdgeTarget()) {
        List<BPLVariableExpression> loopTargets =
          new ArrayList<BPLVariableExpression>();
        LoopTargetDetector loopTargetDetector = new LoopTargetDetector();
        for (String name : loopTargetDetector.detect(cfg, cfgBlock)) {
          // Construct the variables to be havoc'ed.
          loopTargets.add(new BPLVariableExpression(name));
        }

        // Add the havoc command to the new BoogiePL basic block.
        commands.add(new BPLHavocCommand(
            loopTargets.toArray(
                new BPLVariableExpression[loopTargets.size()])));
      }

      // If the basic block is a loop header, we must transform every assert
      // command containing a loop invariant into an assume command. This is the
      // case for every assert command which appears within a prefix of passive
      // commands in the loop header block. Hence, every encountered assert
      // command contains an invariant if and only if we are inside a loop
      // header block and all the commands seen so far are passive. This is
      // exactly what the following flag expresses.
      boolean collectInvariants = cfgBlock.isBackEdgeTarget();
      for (BPLCommand command : cfgBlock.getBPLBlock().getCommands()) {
        if (collectInvariants && (command instanceof BPLAssertCommand)) {
          // We are still collecting loop invariants, so let's turn the assert
          // command into an assume command.
          BPLAssertCommand assertion = (BPLAssertCommand) command;
          commands.add(new BPLAssumeCommand(assertion.getExpression()));
        } else {
          // If we were still collecting loop invariants and the current command
          // is passive, we keep on doing so. Otherwise, we stop collecting
          // loop invariants.
          collectInvariants &= command.isPassive();
          // The current command is no assertion, so let's pass it on as is.
          commands.add(command);
        }
      }

      // Iterate over all successors of the current block and do the following:
      // - If the successor is a loop header block, assume its loop invariants.
      // - Remove all the back edges originating from the current block.
      List<String> targetLabels = new ArrayList<String>();
      Iterator<Edge> outEdges = cfgBlock.outEdgeIterator();
      while (outEdges.hasNext()) {
        Edge outEdge = outEdges.next();
        BasicBlock successor = outEdge.getTarget();

        // Make sure we skip the synthetic entry and exit blocks.
        if (!cfg.isSyntheticBlock(successor)) {
          // If the current successor is a loop header block, we must assert
          // its loop invariants at the end of the current block.
          if (successor.isBackEdgeTarget()) {
            for (BPLExpression inv : getInvariants(successor.getBPLBlock())) {
              commands.add(new BPLAssertCommand(inv));
            }
          }

          // Remove the back edges.
          if (!outEdge.isBackEdge()) {
            targetLabels.add(successor.getBPLBlock().getLabel());
          }
        }
      }

      // Construct the new transfer command for the transformed BoogiePL basic
      // block based on the target labels computed previously.
      BPLTransferCommand transferCommand;
      if (targetLabels.size() == 0) {
        transferCommand = new BPLReturnCommand();
      } else {
        transferCommand = new BPLGotoCommand(
            targetLabels.toArray(new String[targetLabels.size()]));
      }

      // Construct the new BoogiePL basic block.
      return new BPLBasicBlock(
          cfgBlock.getBPLBlock().getLabel(),
          commands.toArray(new BPLCommand[commands.size()]),
          transferCommand);
    }

    /**
     * Returns a list of expressions representing the loop invariants of the
     * given BoogiePL {@code block}. These correspond to the expressions of all
     * the <tt>assert</tt> commands appearing within a prefix of <i>passive</i>
     * BoogiePL commands in the given BoogiePL {@code block}.
     *
     * @param block  The BoogiePL block whose loop invariants to return.
     * @return       A list of expressions representing the loop invariants of
     *               the given BoogiePL {@code block}.
     */
    private List<BPLExpression> getInvariants(BPLBasicBlock block) {
      List<BPLExpression> invariants = new ArrayList<BPLExpression>();
      for (BPLCommand command : block.getCommands()) {
        if (command instanceof BPLAssertCommand) {
          // Collect the expressions of all the assert commands.
          BPLAssertCommand assertion = (BPLAssertCommand) command;
          invariants.add(assertion.getExpression());
        } else if (!command.isPassive()) {
          // If the current command is not passive, we must stop collecting the
          // loop invariants.
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
      // Axioms may be passed on without any transformation.
      declarations.add(axiom);
      return null;
    }

    public Object visitConstantDeclaration(BPLConstantDeclaration declaration) {
      // Constant declarations may be passed on without any transformation.
      declarations.add(declaration);
      return null;
    }

    public Object visitImplementation(BPLImplementation implementation) {
      // Pass on a new implementation whose body has been transformed.
      declarations.add(new BPLImplementation(
          implementation.getProcedureName(),
          implementation.getInParameters(),
          implementation.getOutParameters(),
          transformLoops(implementation.getBody())));
      return null;
    }

    public Object visitProcedure(BPLProcedure procedure) {
      if (procedure.getBody() == null) {
        // If a procedure has no implementation body, it may be passed on
        // without any transformation.
        declarations.add(procedure);
      } else {
        // Pass on a new procedure whose body has been transformed.
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
      // Type declarations may be passed on without any transformation.
      declarations.add(declaration);
      return null;
    }

    public Object visitVariableDeclaration(BPLVariableDeclaration declaration) {
      // Variable declarations may be passed on without any transformation.
      declarations.add(declaration);
      return null;
    }

    public Object visitFunction(BPLFunction function) {
      // Function declarations may be passed on without any transformation.
      declarations.add(function);
      return null;
    }
  }
}
