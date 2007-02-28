package b2bpl.bytecode.analysis;

import java.util.HashMap;
import java.util.HashSet;

import b2bpl.bytecode.BCMethod;
import b2bpl.bytecode.ExceptionHandler;
import b2bpl.bytecode.InstructionHandle;
import b2bpl.bytecode.InstructionVisitor;
import b2bpl.bytecode.Instructions;
import b2bpl.bytecode.JClassType;
import b2bpl.bytecode.JNullType;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.TypeLoader;
import b2bpl.bytecode.instructions.AALoadInstruction;
import b2bpl.bytecode.instructions.AAStoreInstruction;
import b2bpl.bytecode.instructions.AConstNullInstruction;
import b2bpl.bytecode.instructions.ALoadInstruction;
import b2bpl.bytecode.instructions.ANewArrayInstruction;
import b2bpl.bytecode.instructions.AReturnInstruction;
import b2bpl.bytecode.instructions.AStoreInstruction;
import b2bpl.bytecode.instructions.AThrowInstruction;
import b2bpl.bytecode.instructions.AbstractIfInstruction;
import b2bpl.bytecode.instructions.ArrayLengthInstruction;
import b2bpl.bytecode.instructions.CheckCastInstruction;
import b2bpl.bytecode.instructions.Dup2Instruction;
import b2bpl.bytecode.instructions.Dup2X1Instruction;
import b2bpl.bytecode.instructions.Dup2X2Instruction;
import b2bpl.bytecode.instructions.DupInstruction;
import b2bpl.bytecode.instructions.DupX1Instruction;
import b2bpl.bytecode.instructions.DupX2Instruction;
import b2bpl.bytecode.instructions.GetFieldInstruction;
import b2bpl.bytecode.instructions.GetStaticInstruction;
import b2bpl.bytecode.instructions.GotoInstruction;
import b2bpl.bytecode.instructions.IBinArithInstruction;
import b2bpl.bytecode.instructions.IBitwiseInstruction;
import b2bpl.bytecode.instructions.IIncInstruction;
import b2bpl.bytecode.instructions.ILoadInstruction;
import b2bpl.bytecode.instructions.INegInstruction;
import b2bpl.bytecode.instructions.IReturnInstruction;
import b2bpl.bytecode.instructions.IStoreInstruction;
import b2bpl.bytecode.instructions.IfACmpInstruction;
import b2bpl.bytecode.instructions.IfICmpInstruction;
import b2bpl.bytecode.instructions.IfInstruction;
import b2bpl.bytecode.instructions.IfNonNullInstruction;
import b2bpl.bytecode.instructions.IfNullInstruction;
import b2bpl.bytecode.instructions.InstanceOfInstruction;
import b2bpl.bytecode.instructions.Instruction;
import b2bpl.bytecode.instructions.InvokeInstruction;
import b2bpl.bytecode.instructions.InvokeInterfaceInstruction;
import b2bpl.bytecode.instructions.InvokeSpecialInstruction;
import b2bpl.bytecode.instructions.InvokeStaticInstruction;
import b2bpl.bytecode.instructions.InvokeVirtualInstruction;
import b2bpl.bytecode.instructions.LBinArithInstruction;
import b2bpl.bytecode.instructions.LBitwiseInstruction;
import b2bpl.bytecode.instructions.LCmpInstruction;
import b2bpl.bytecode.instructions.LLoadInstruction;
import b2bpl.bytecode.instructions.LNegInstruction;
import b2bpl.bytecode.instructions.LReturnInstruction;
import b2bpl.bytecode.instructions.LStoreInstruction;
import b2bpl.bytecode.instructions.LdcInstruction;
import b2bpl.bytecode.instructions.LookupSwitchInstruction;
import b2bpl.bytecode.instructions.MultiANewArrayInstruction;
import b2bpl.bytecode.instructions.NewArrayInstruction;
import b2bpl.bytecode.instructions.NewInstruction;
import b2bpl.bytecode.instructions.NopInstruction;
import b2bpl.bytecode.instructions.Pop2Instruction;
import b2bpl.bytecode.instructions.PopInstruction;
import b2bpl.bytecode.instructions.PutFieldInstruction;
import b2bpl.bytecode.instructions.PutStaticInstruction;
import b2bpl.bytecode.instructions.ReturnInstruction;
import b2bpl.bytecode.instructions.SwapInstruction;
import b2bpl.bytecode.instructions.TableSwitchInstruction;
import b2bpl.bytecode.instructions.VALoadInstruction;
import b2bpl.bytecode.instructions.VAStoreInstruction;
import b2bpl.bytecode.instructions.VCastInstruction;
import b2bpl.bytecode.instructions.VConstantInstruction;


/**
 * Builds up a {@link ControlFlowGraph} for a given bytecode method.
 *
 * <p>
 * The {@code ControlFlowGraph} created models the normal as well as exceptional
 * program flow of the given method and can optionally be configured to model
 * the runtime exceptions implicitly thrown by some of the bytecode
 * instructions.
 * </p>
 *
 * @see ControlFlowGraph
 *
 * @author Ovidio Mallo
 */
public class CFGBuilder {

  /**
   * Whether to explicitly model the runtime exceptions thrown by some bytecode
   * instructions in the control flow graph.
   */
  private final boolean modelRuntimeExceptions;

  /**
   * The bytecode method for which the control flow graph is being constructed.
   */
  private BCMethod method;

  /** The control flow graph being constructed. */
  private ControlFlowGraph cfg;

  /** Maps the instruction leading a basic block to that block. */
  private HashMap<InstructionHandle, BasicBlock> blocks;

  /**
   * Maps the instruction at the end of a basic block to its set of succhessor
   * blocks.
   */
  private HashMap<InstructionHandle, HashSet<BasicBlock>> successorBlocks;

  /**
   * Instantiates a new control flow graph builder which is configured once and
   * which can then be used to construct control flow graphs for different
   * bytecode methods.
   *
   * @param modelRuntimeExceptions  Whether to explicitly model the runtime
   *                                exceptions thrown by some bytecode
   *                                instructions in the control flow graph.
   */
  public CFGBuilder(boolean modelRuntimeExceptions) {
    this.modelRuntimeExceptions = modelRuntimeExceptions;
  }

  /**
   * Builds up a control flow graph for the given bytecode {@code method}.
   *
   * @param method  The bytecode method for which to construct the control flow
   *                graph.
   * @return        The control flow graph for the given bytecode
   *                {@code method}.
   */
  public ControlFlowGraph build(BCMethod method) {
    this.method = method;

    // Initialize the internal datastructures.
    blocks = new HashMap<InstructionHandle, BasicBlock>();
    successorBlocks = new HashMap<InstructionHandle, HashSet<BasicBlock>>();

    Instructions instructions = method.getInstructions();
    cfg = new ControlFlowGraph();

    // Connect the synthetic entry block created for every control flow graph
    // to the basic block starting at the first instruction of the method.
    cfg.getEntryBlock().addSuccessor(startBlockAt(instructions.get(0)));

    Builder builder = new Builder();
    for (InstructionHandle instruction : instructions) {
      // If the stack frame of the instruction is not set, the instruction
      // is not reachable, so we may simply skip it.
      if (instruction.getFrame() != null) {
        // Update the instruction handle on the actual builder before visiting
        // the instruction.
        builder.handle = instruction;
        // Handle the control flow due to the current instruction.
        instruction.accept(builder);

        if (modelRuntimeExceptions) {
          Instruction insn = instruction.getInstruction();
          // Explicitly model the program flow cause by the runtime exceptions
          // thrown by the current instruction.
          for (String rtException : insn.getRuntimeExceptions()) {
            JType exception = TypeLoader.getClassType(rtException);
            addRuntimeExceptionEdges(instruction, exception);
          }

          // If the instruction throws any runtime exception, we must add a
          // fallthrough edge to the next instruction unless the instruction
          // is an unconditional branch (such as the ATHROW instruction).
          if ((insn.getRuntimeExceptions().length > 0)
              && !insn.isUnconditionalBranch()) {
            addEdge(instruction, instruction.getNext());
          }
        }
      }
    }

    // Once we have visited all the method's instructions, we can finally build
    // up the control flow graph using the information collected.

    // We go through all the instructions while detecting the boundaries of
    // basic blocks.
    InstructionHandle first = instructions.get(0);
    while (first != null) {
      InstructionHandle last = first;
      // As long as the current instruction has no successor blocks and the next
      // instructions is not the leader of a basic block, we have not found the
      // end of the basic block.
      while ((successorBlocks.get(last) == null)
             && (blocks.get(last.getNext()) == null)) {
        last = last.getNext();
      }

      // Set the range of instructions on the corresponding basic block.
      BasicBlock block = blocks.get(first);
      block.setInstructions(first, last);

      HashSet<BasicBlock> successors = successorBlocks.get(last);
      if (successors != null) {
        // If the last instruction explicitly gives rise to branches in the
        // program flow, we add all the targets as successors of the current
        // basic block.
        for (BasicBlock successor : successors) {
          block.addSuccessor(successor);
        }
      } else {
        // Even if the last instruction of the basic block does not itself give
        // rise to branches in the program flow, we must still add a fallthrough
        // edge to the next instruction.
        block.addSuccessor(blocks.get(last.getNext()));
      }

      cfg.addBlock(block);

      // Move to the instruction right after the current basic block.
      first = last.getNext();

      // Skip any unreachable instructions.
      while ((first != null) && (blocks.get(first) == null)) {
        first = first.getNext();
      }
    }

    return cfg;
  }

  /**
   * Adds an edge between the given {@code source} and {@code target}
   * instructions to the control flow graph.
   *
   * @param source  The source instruction of the edge.
   * @param target  The target instruction of the edge.
   */
  private void addEdge(InstructionHandle source, InstructionHandle target) {
    // Start a new basic block at the target instruction and add it to the set
    // of successors of the source instruction.
    addSuccessor(source, startBlockAt(target));
  }

  /**
   * Adds an edge from the given {@code source} instruction to the synthetic
   * exit block of the control flow graph.
   *
   * @param source  The source instruction of the edge.
   */
  private void addExitEdge(InstructionHandle source) {
    addSuccessor(source, cfg.getExitBlock());
  }

  /**
   * Adds the given {@code successor} basic block to the set of successors of
   * the given {@code source} instruction.
   *
   * @param source     The source instruction of the edge.
   * @param successor  The basic block of the instruction's successor.
   */
  private void addSuccessor(InstructionHandle source, BasicBlock successor) {
    HashSet<BasicBlock> successors = successorBlocks.get(source);
    if (successors == null) {
      successors = new HashSet<BasicBlock>();
      successorBlocks.put(source, successors);
    }
    successors.add(successor);
  }

  /**
   * Adds an edge from the given {@code source} instruction to any exception
   * handler which may catch the given {@code exception} at runtime. If the
   * exception may not be caught inside the current method, an edge from the
   * {@code source} instruction to the synthetic exit block of the control flow
   * graph is also added.
   *
   * @param source     The instruction throwing the given {@code exception}.
   * @param exception  The exception thrown by the instruction.
   */
  private void addExceptionEdges(InstructionHandle source, JType exception) {
    // The tightest exception handler type found so far. This is required since
    // exception handlers appearing later on whose handler type is a subtype of
    // this type will never catch the current exception.
    JType tightestHandlerType = JNullType.NULL;
    for (ExceptionHandler handler : method.getExceptionHandlers()) {
      if (handler.isActiveFor(source)) {
        JType handlerType = handler.getType();
        if (exception.isSubtypeOf(handlerType)) {
          // The exception type is a subtype of the handler's type meaning that
          // no further exception handlers will ever catch this exception at
          // runtime. Therefore, we can return from the method.
          addEdge(source, handler.getHandler());
          return;
        } else if (handlerType.isSubtypeOf(exception)
            && tightestHandlerType.isProperSubtypeOf(handlerType)) {
          // The exception type is a supertype of the handler's type, so we keep
          // on looking at the exception handlers.
          addEdge(source, handler.getHandler());
          tightestHandlerType = handlerType;
        }
      }
    }

    // If we get to this point, the exception may not have been caught by any
    // exception handler, so we must add an edge from the source instruction
    // to the synthetic exit block of the control flow graph.
    addExitEdge(source);
  }

  /**
   * Adds an edge from the given {@code source} instruction to any exception
   * handler which may catch the given runtime {@code exception} at runtime. If
   * the exception may not be caught inside the current method, an edge from the
   * {@code source} instruction to the synthetic exit block of the control flow
   * graph is also added.
   *
   * @param source     The instruction throwing the given runtime
   *                   {@code exception}.
   * @param exception  The runtime exception thrown by the instruction.
   */
  private void addRuntimeExceptionEdges(
      InstructionHandle source,
      JType exception) {
    // For runtime exceptions we know the exact runtime type of the exception
    // so only exception handlers for supertypes of the runtime exception type
    // are possible candidates.
    for (ExceptionHandler handler : method.getExceptionHandlers()) {
      if (handler.isActiveFor(source)) {
        if (exception.isSubtypeOf(handler.getType())) {
          addEdge(source, handler.getHandler());
          return;
        }
      }
    }

    // If we get to this point, the runtime exception is not caught by any
    // exception handler, so we must add an edge from the source instruction
    // to the synthetic exit block of the control flow graph.
    addExitEdge(source);
  }

  /**
   * Starts a new basic block in the control flow graph at the given instruction
   * {@code first}.
   *
   * @param first  The instruction at which to start a new basic block.
   * @return       The new basic block starting at the given instruction.
   */
  private BasicBlock startBlockAt(InstructionHandle first) {
    BasicBlock block = blocks.get(first);
    if (block == null) {
      block = new BasicBlock();
      blocks.put(first, block);
    }
    return block;
  }

  /**
   * The visitor triggering the generation of the basic blocks and edges in the
   * control flow graph for the individual instructions of the method.
   *
   * @author Ovidio Mallo
   */
  private final class Builder implements InstructionVisitor {

    /**
     * The instruction handle of the instruction being visited. Should be
     * updated by the {@code CFGBuilder} as appropriate.
     */
    private InstructionHandle handle;

    public void visitNopInstruction(NopInstruction insn) {
      // do nothing
    }

    public void visitILoadInstruction(ILoadInstruction insn) {
      // do nothing
    }

    public void visitLLoadInstruction(LLoadInstruction insn) {
      // do nothing
    }

    public void visitALoadInstruction(ALoadInstruction insn) {
      // do nothing
    }

    public void visitIStoreInstruction(IStoreInstruction insn) {
      // do nothing
    }

    public void visitLStoreInstruction(LStoreInstruction insn) {
      // do nothing
    }

    public void visitAStoreInstruction(AStoreInstruction insn) {
      // do nothing
    }

    public void visitVConstantInstruction(VConstantInstruction insn) {
      // do nothing
    }

    public void visitLdcInstruction(LdcInstruction insn) {
      // do nothing
    }

    public void visitAConstNullInstruction(AConstNullInstruction insn) {
      // do nothing
    }

    public void visitGetFieldInstruction(GetFieldInstruction insn) {
      // do nothing
    }

    public void visitPutFieldInstruction(PutFieldInstruction insn) {
      // do nothing
    }

    public void visitGetStaticInstruction(GetStaticInstruction insn) {
      // do nothing
    }

    public void visitPutStaticInstruction(PutStaticInstruction insn) {
      // do nothing
    }

    public void visitVALoadInstruction(VALoadInstruction insn) {
      // do nothing
    }

    public void visitAALoadInstruction(AALoadInstruction insn) {
      // do nothing
    }

    public void visitVAStoreInstruction(VAStoreInstruction insn) {
      // do nothing
    }

    public void visitAAStoreInstruction(AAStoreInstruction insn) {
      // do nothing
    }

    public void visitArrayLengthInstruction(ArrayLengthInstruction insn) {
      // do nothing
    }

    private void handleInvokeInstruction(InvokeInstruction insn) {
      JClassType[] exceptions = insn.getMethod().getExceptionTypes();
      for (JClassType exception : exceptions) {
        addExceptionEdges(handle, exception);
      }
      if (exceptions.length > 0) {
        addEdge(handle, handle.getNext());
      }
    }

    public void visitInvokeVirtualInstruction(InvokeVirtualInstruction insn) {
      handleInvokeInstruction(insn);
    }

    public void visitInvokeStaticInstruction(InvokeStaticInstruction insn) {
      handleInvokeInstruction(insn);
    }

    public void visitInvokeSpecialInstruction(InvokeSpecialInstruction insn) {
      handleInvokeInstruction(insn);
    }

    public void visitInvokeInterfaceInstruction(
        InvokeInterfaceInstruction insn) {
      handleInvokeInstruction(insn);
    }

    public void visitIBinArithInstruction(IBinArithInstruction insn) {
      // do nothing
    }

    public void visitLBinArithInstruction(LBinArithInstruction insn) {
      // do nothing
    }

    public void visitIBitwiseInstruction(IBitwiseInstruction insn) {
      // do nothing
    }

    public void visitLBitwiseInstruction(LBitwiseInstruction insn) {
      // do nothing
    }

    public void visitINegInstruction(INegInstruction insn) {
      // do nothing
    }

    public void visitLNegInstruction(LNegInstruction insn) {
      // do nothing
    }

    public void visitIIncInstruction(IIncInstruction insn) {
      // do nothing
    }

    private void handleIfInstruction(AbstractIfInstruction insn) {
      addEdge(handle, insn.getTarget());
      addEdge(handle, handle.getNext());
    }

    public void visitIfICmpInstruction(IfICmpInstruction insn) {
      handleIfInstruction(insn);
    }

    public void visitIfACmpInstruction(IfACmpInstruction insn) {
      handleIfInstruction(insn);
    }

    public void visitIfInstruction(IfInstruction insn) {
      handleIfInstruction(insn);
    }

    public void visitIfNonNullInstruction(IfNonNullInstruction insn) {
      handleIfInstruction(insn);
    }

    public void visitIfNullInstruction(IfNullInstruction insn) {
      handleIfInstruction(insn);
    }

    public void visitLCmpInstruction(LCmpInstruction insn) {
      // do nothing
    }

    public void visitGotoInstruction(GotoInstruction insn) {
      addEdge(handle, insn.getTarget());
    }

    public void visitLookupSwitchInstruction(LookupSwitchInstruction insn) {
      for (InstructionHandle target : insn.getTargets()) {
        addEdge(handle, target);
      }
      addEdge(handle, insn.getDefaultTarget());
    }

    public void visitTableSwitchInstruction(TableSwitchInstruction insn) {
      for (InstructionHandle target : insn.getTargets()) {
        addEdge(handle, target);
      }
      addEdge(handle, insn.getDefaultTarget());
    }

    public void visitReturnInstruction(ReturnInstruction insn) {
      addExitEdge(handle);
    }

    public void visitIReturnInstruction(IReturnInstruction insn) {
      addExitEdge(handle);
    }

    public void visitLReturnInstruction(LReturnInstruction insn) {
      addExitEdge(handle);
    }

    public void visitAReturnInstruction(AReturnInstruction insn) {
      addExitEdge(handle);
    }

    public void visitAThrowInstruction(AThrowInstruction insn) {
      JType exception = handle.getFrame().peek();
      addExceptionEdges(handle, exception);
    }

    public void visitNewInstruction(NewInstruction insn) {
      // do nothing
    }

    public void visitNewArrayInstruction(NewArrayInstruction insn) {
      // do nothing
    }

    public void visitANewArrayInstruction(ANewArrayInstruction insn) {
      // do nothing
    }

    public void visitMultiANewArrayInstruction(MultiANewArrayInstruction insn) {
      // do nothing
    }

    public void visitCheckCastInstruction(CheckCastInstruction insn) {
      // do nothing
    }

    public void visitVCastInstruction(VCastInstruction insn) {
      // do nothing
    }

    public void visitInstanceOfInstruction(InstanceOfInstruction insn) {
      // do nothing
    }

    public void visitPopInstruction(PopInstruction insn) {
      // do nothing
    }

    public void visitPop2Instruction(Pop2Instruction insn) {
      // do nothing
    }

    public void visitSwapInstruction(SwapInstruction insn) {
      // do nothing
    }

    public void visitDupInstruction(DupInstruction insn) {
      // do nothing
    }

    public void visitDup2Instruction(Dup2Instruction insn) {
      // do nothing
    }

    public void visitDupX1Instruction(DupX1Instruction insn) {
      // do nothing
    }

    public void visitDupX2Instruction(DupX2Instruction insn) {
      // do nothing
    }

    public void visitDup2X1Instruction(Dup2X1Instruction insn) {
      // do nothing
    }

    public void visitDup2X2Instruction(Dup2X2Instruction insn) {
      // do nothing
    }
  }
}
