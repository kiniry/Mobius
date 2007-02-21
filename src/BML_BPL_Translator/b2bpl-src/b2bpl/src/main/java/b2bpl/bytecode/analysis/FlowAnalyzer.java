package b2bpl.bytecode.analysis;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.FrameNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LineNumberNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.AnalyzerException;
import org.objectweb.asm.tree.analysis.BasicValue;
import org.objectweb.asm.tree.analysis.Frame;
import org.objectweb.asm.tree.analysis.SimpleVerifier;
import org.objectweb.asm.tree.analysis.Value;

import b2bpl.bytecode.BCMethod;
import b2bpl.bytecode.ExceptionHandler;
import b2bpl.bytecode.InstructionHandle;
import b2bpl.bytecode.Instructions;
import b2bpl.bytecode.JArrayType;
import b2bpl.bytecode.JBaseType;
import b2bpl.bytecode.JClassType;
import b2bpl.bytecode.JNullType;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.TypeLoader;
import b2bpl.bytecode.instructions.AThrowInstruction;
import b2bpl.bytecode.instructions.Instruction;
import b2bpl.bytecode.instructions.InvokeInstruction;


public class FlowAnalyzer extends Analyzer {

  private Instructions insns;

  private int[] map;

  private List<ExceptionHandler>[] activeHandlers;

  private final boolean modelRuntimeExceptions;

  public FlowAnalyzer(boolean modelRuntimeExceptions) {
    super(new Verifier());
    this.modelRuntimeExceptions = modelRuntimeExceptions;
  }

  public Frame[] analyze(String owner, MethodNode asmMethod)
      throws AnalyzerException {
    JClassType ownerType = TypeLoader.getClassType(owner);
    BCMethod method = ownerType.getMethod(asmMethod.name, asmMethod.desc);
    insns = method.getInstructions();

    computeMap(asmMethod.instructions);

    activeHandlers = new List[insns.size()];
    for (int i = 0; i < insns.size(); i++) {
      activeHandlers[i] = new ArrayList<ExceptionHandler>();
    }

    ExceptionHandler[] handlers = method.getExceptionHandlers();
    for (ExceptionHandler handler : handlers) {
      int start = handler.getStart().getIndex();
      int end = handler.getEnd().getIndex();
      for (int i = start; i < end; i++) {
        activeHandlers[i].add(handler);
      }
    }

    Frame[] asmFrames = super.analyze(owner, asmMethod);

    for (int i = 0; i < asmFrames.length; i++) {
      insns.get(map[i]).setFrame(
          convertFrame(asmFrames[i], asmMethod.maxLocals, asmMethod.maxStack));
    }

    return asmFrames;
  }

  private void computeMap(InsnList asmInsns) {
    map = new int[asmInsns.size()];
    int insnIndex = 0;
    for (int i = 0; i < asmInsns.size(); i++) {
      map[i] = insnIndex;

      AbstractInsnNode asmInsn = asmInsns.get(i);
      if (!(asmInsn instanceof LabelNode)
          && !(asmInsn instanceof FrameNode)
          && !(asmInsn instanceof LineNumberNode)) {
        insnIndex++;
      }
    }
  }

  protected boolean newControlFlowExceptionEdge(int insn, int successor) {
    return newControlFlowExceptionEdge(
        insns.get(map[insn]),
        insns.get(map[successor]),
        getFrames()[insn]);
  }

  private boolean newControlFlowExceptionEdge(
      InstructionHandle insn,
      InstructionHandle successor,
      Frame insnFrame) {
    List<JType> exceptions = computeExceptions(insn, insnFrame);
    for (JType exception : exceptions) {
      JType tightestHandlerType = JNullType.NULL;
      for (ExceptionHandler handler : activeHandlers[insn.getIndex()]) {
        JType handlerType = handler.getType();
        if (exception.isSubtypeOf(handlerType)) {
          return successor == handler.getHandler();
        } else if (handlerType.isSubtypeOf(exception)
            && tightestHandlerType.isProperSubtypeOf(handlerType)) {
          if (handler.getHandler() == successor) {
            return true;
          }
          tightestHandlerType = handlerType;
        }
      }
    }

    if (modelRuntimeExceptions) {
      Instruction instruction = insn.getInstruction();
      for (String runtimeException : instruction.getRuntimeExceptions()) {
        JType exception = TypeLoader.getClassType(runtimeException);
        for (ExceptionHandler handler : activeHandlers[insn.getIndex()]) {
          JType handlerType = handler.getType();
          if (exception.isSubtypeOf(handlerType)) {
            return successor == handler.getHandler();
          }
        }
      }
    }

    return false;
  }

  private static List<JType> computeExceptions(
      InstructionHandle insn,
      Frame insnFrame) {
    Instruction instruction = insn.getInstruction();
    List<JType> exceptions = new ArrayList<JType>();

    if (instruction == AThrowInstruction.ATHROW) {
      Value thrownValue = insnFrame.getStack(insnFrame.getStackSize() - 1);
      Type thrownType = ((BasicValue) thrownValue).getType();
      exceptions.add(convertType(thrownType));
    } else if (instruction instanceof InvokeInstruction) {
      BCMethod method = ((InvokeInstruction) instruction).getMethod();
      exceptions.addAll(Arrays.asList(method.getExceptionTypes()));
    }

    return exceptions;
  }

  private static ExecutionFrame convertFrame(
      Frame asmFrame,
      int maxLocals,
      int maxStack) {
    if (asmFrame != null) {
      ExecutionFrame frame = new ExecutionFrame(maxLocals, maxStack);
      for (int i = 0; i < maxLocals; i++) {
        Type asmType = ((BasicValue) asmFrame.getLocal(i)).getType();
        frame.setLocal(i, convertType(asmType));
      }
      for (int i = 0; i < asmFrame.getStackSize(); i++) {
        Type asmType = ((BasicValue) asmFrame.getStack(i)).getType();
        frame.push(convertType(asmType));
      }
      return frame;
    }
    return null;
  }

  private static JType convertType(Type asmType) {
    if (asmType != null) {
      switch (asmType.getSort()) {
        case Type.INT:
          return JBaseType.INT;
        case Type.SHORT:
          return JBaseType.SHORT;
        case Type.BYTE:
          return JBaseType.BYTE;
        case Type.CHAR:
          return JBaseType.CHAR;
        case Type.BOOLEAN:
          return JBaseType.BOOLEAN;
        case Type.LONG:
          return JBaseType.LONG;
        case Type.FLOAT:
          return JBaseType.FLOAT;
        case Type.DOUBLE:
          return JBaseType.DOUBLE;
        case Type.OBJECT:
          if (asmType.getDescriptor().equals("Lnull;")) {
            return JNullType.NULL;
          }
          return TypeLoader.getClassType(asmType.getClassName());
        case Type.ARRAY:
          JType elementType = convertType(asmType.getElementType());
          return new JArrayType(elementType, asmType.getDimensions());
      }
    }
    return null;
  }

  private static final class Verifier extends SimpleVerifier {

    protected boolean isInterface(Type t) {
      JType type = convertType(t);
      if (type.isClassType()) {
        return ((JClassType) type).isInterface();
      }
      return false;
    }

    protected Type getSuperClass(Type t) {
      JType type = convertType(t);
      JType supertype = null;
      if (type.isClassType()) {
        supertype = ((JClassType) type).getSupertype();
      } else if (type.isArrayType()) {
        supertype = TypeLoader.getClassType("java.lang.Object");
      }
      if (supertype != null) {
        return Type.getType(supertype.getDescriptor());
      }
      return null;
    }

    protected boolean isSubTypeOf(final Value value, final Value expected) {
      JType subtype = convertType(((BasicValue) value).getType());
      JType supertype = convertType(((BasicValue) expected).getType());
      return subtype.isSubtypeOf(supertype);
    }

    protected boolean isAssignableFrom(Type t, Type u) {
      JType src = convertType(u);
      JType dst = convertType(t);
      return src.isSubtypeOf(dst);
    }
  }
}
