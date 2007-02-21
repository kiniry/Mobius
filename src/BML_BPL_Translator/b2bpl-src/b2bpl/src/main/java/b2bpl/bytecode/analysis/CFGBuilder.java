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
import b2bpl.bytecode.instructions.VALoadInstruction;
import b2bpl.bytecode.instructions.VAStoreInstruction;
import b2bpl.bytecode.instructions.IBinArithInstruction;
import b2bpl.bytecode.instructions.IBitwiseInstruction;
import b2bpl.bytecode.instructions.IConstantInstruction;
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
import b2bpl.bytecode.instructions.VCastInstruction;


public class CFGBuilder {

  private final boolean modelRuntimeExceptions;

  private BCMethod method;

  private ControlFlowGraph cfg;

  private HashMap<InstructionHandle, BasicBlock> blocks;

  private HashMap<InstructionHandle, HashSet<BasicBlock>> successorBlocks;

  public CFGBuilder(boolean modelRuntimeExceptions) {
    this.modelRuntimeExceptions = modelRuntimeExceptions;
  }

  public ControlFlowGraph build(BCMethod method) {
    this.method = method;

    blocks = new HashMap<InstructionHandle, BasicBlock>();
    successorBlocks = new HashMap<InstructionHandle, HashSet<BasicBlock>>();

    Instructions instructions = method.getInstructions();
    cfg = new ControlFlowGraph();
    cfg.getEntryBlock().addSuccessor(startBlockAt(instructions.get(0)));

    Builder builder = new Builder();
    for (InstructionHandle instruction : instructions) {
      // If the stack frame of the instruction is not set, the instruction
      // is not reachable, so we may simply skip it.
      if (instruction.getFrame() != null) {
        builder.handle = instruction;
        instruction.accept(builder);
        if (modelRuntimeExceptions) {
          Instruction insn = instruction.getInstruction();
          for (String rtException : insn.getRuntimeExceptions()) {
            JType exception = TypeLoader.getClassType(rtException);
            addRuntimeExceptionEdges(instruction, exception);
          }
          if ((insn.getRuntimeExceptions().length > 0)
              && !insn.isUnconditionalBranch()) {
            addEdge(instruction, instruction.getNext());
          }
        }
      }
    }

    InstructionHandle first = instructions.get(0);
    while (first != null) {
      BasicBlock block = blocks.get(first);
      InstructionHandle last = first;
      while ((successorBlocks.get(last) == null)
             && (blocks.get(last.getNext()) == null)) {
        last = last.getNext();
      }
      block.setInstructions(first, last);
      HashSet<BasicBlock> successors = successorBlocks.get(last);
      if (successors != null) {
        for (BasicBlock successor : successors) {
          block.addSuccessor(successor);
        }
      } else {
        block.addSuccessor(blocks.get(last.getNext()));
      }
      cfg.addBlock(block);
      first = last.getNext();
      while ((first != null) && (blocks.get(first) == null)) {
        first = first.getNext();
      }
    }

    return cfg;
  }

  public ControlFlowGraph getCFG() {
    return cfg;
  }

  private void addEdge(InstructionHandle source, InstructionHandle target) {
    addSuccessor(source, startBlockAt(target));
  }

  private void addExitEdge(InstructionHandle source) {
    addSuccessor(source, cfg.getExitBlock());
  }

  private void addSuccessor(InstructionHandle source, BasicBlock target) {
    HashSet<BasicBlock> successors = successorBlocks.get(source);
    if (successors == null) {
      successors = new HashSet<BasicBlock>();
      successorBlocks.put(source, successors);
    }
    successors.add(target);
  }

  private void addExceptionEdges(InstructionHandle source, JType exception) {
    JType tightestHandlerType = JNullType.NULL;
    for (ExceptionHandler handler : method.getExceptionHandlers()) {
      if (handler.isActiveFor(source)) {
        JType handlerType = handler.getType();
        if (exception.isSubtypeOf(handlerType)) {
          addEdge(source, handler.getHandler());
          return;
        } else if (handlerType.isSubtypeOf(exception)
            && tightestHandlerType.isProperSubtypeOf(handlerType)) {
          addEdge(source, handler.getHandler());
          tightestHandlerType = handlerType;
        }
      }
    }
    addExitEdge(source);
  }

  private void addRuntimeExceptionEdges(
      InstructionHandle source,
      JType exception) {
    for (ExceptionHandler handler : method.getExceptionHandlers()) {
      if (handler.isActiveFor(source)) {
        if (exception.isSubtypeOf(handler.getType())) {
          addEdge(source, handler.getHandler());
          return;
        }
      }
    }
    addExitEdge(source);
  }

  private BasicBlock startBlockAt(InstructionHandle first) {
    BasicBlock block = blocks.get(first);
    if (block == null) {
      block = new BasicBlock();
      blocks.put(first, block);
    }
    return block;
  }

  private final class Builder implements InstructionVisitor {

    private InstructionHandle handle;

    public void visitNopInstruction(NopInstruction insn) {
      // do nothing
    }

    public void visitILoadInstruction(ILoadInstruction insn) {
      // do nothing
    }

    public void visitALoadInstruction(ALoadInstruction insn) {
      // do nothing
    }

    public void visitIStoreInstruction(IStoreInstruction insn) {
      // do nothing
    }

    public void visitAStoreInstruction(AStoreInstruction insn) {
      // do nothing
    }

    public void visitIConstantInstruction(IConstantInstruction insn) {
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

    public void visitIBitwiseInstruction(IBitwiseInstruction insn) {
      // do nothing
    }

    public void visitINegInstruction(INegInstruction insn) {
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
