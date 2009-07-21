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
import b2bpl.bytecode.instructions.InvokeSpecialInstruction;


/**
 * Performs the dataflow analysis on a given bytecode method.
 *
 * <p>
 * The actual dataflow analysis algorithm is performed by the ASM bytecode
 * library which in turn relies on some information being provided by subclasses
 * of the {@code Analyzer} class as this one.
 * </p>
 *
 * @author Ovidio Mallo
 */
public class FlowAnalyzer extends Analyzer {

  /**
   * Whether to explicitly model the runtime exceptions thrown by some bytecode
   * instructions in the program flow.
   */
  private final boolean modelRuntimeExceptions;

  /** The bytecode method being analyzed. */
  private BCMethod method;

  /**
   * A map from the bytecode instructions as represented in the ASM bytecode
   * library to the instructions as represented inside a {@code BCMethod} of the
   * translator.
   */
  private int[] map;

  /**
   * The exception handlers active at the individual instructions of the
   * {@code BCMethod} being analyzed.
   */
  @SuppressWarnings("unchecked")
  private List<ExceptionHandler>[] activeHandlers;

  /**
   * Instantiates a new flow analyzer which is configured once and which can
   * then be used to analyze different bytecode methods.
   *
   * @param modelRuntimeExceptions  Whether to explicitly model the runtime
   *                                exceptions thrown by some bytecode
   *                                instructions in the program flow.
   */
  public FlowAnalyzer(boolean modelRuntimeExceptions) {
    super(new Verifier());
    this.modelRuntimeExceptions = modelRuntimeExceptions;
  }

  /**
   * Analyzes the bytecode method belonging to the given {@code owner} type and
   * represented by the {@code asmMethod} which is the representation of the
   * method in the ASM bytecode library. The actual analysis, however, is
   * performed on the corresponding instance of a {@code BCMethod} as used in
   * the translator. This method guarantees that all the JVM stack frames of the
   * all the <i>reachable</i> bytecode instructions of the latter have been
   * computed.
   *
   * @param owner      The type name of the method's owner.
   * @param asmMethod  The ASM representation of the method.
   * @return           The ASM stack frames of the individual instructions.
   */
  public Frame[] analyze(String owner, MethodNode asmMethod) throws AnalyzerException {
    
    if (asmMethod == null) return null;
    
    JClassType ownerType = TypeLoader.getClassType(owner);
       
    method = ownerType.getMethod(asmMethod.name, asmMethod.desc);
    Instructions insns = method.getInstructions();

    computeMap(asmMethod.instructions);

    // Initialize the flag as of whether the this object has been initialized
    // at the individual bytecode methods.
    for (InstructionHandle insn : insns) {
      // The flag is set to true unless the method is a constructor.
      insn.setThisInitialized(!method.isConstructor());
    }

    activeHandlers = new List[insns.size()];
    for (int i = 0; i < insns.size(); i++) {
      activeHandlers[i] = new ArrayList<ExceptionHandler>();
    }

    // Compute the active handlers at the individual instructions.
    ExceptionHandler[] handlers = method.getExceptionHandlers();
    for (ExceptionHandler handler : handlers) {
      int start = handler.getStart().getIndex();
      int end = handler.getEnd().getIndex();
      for (int i = start; i < end; i++) {
        activeHandlers[i].add(handler);
      }
    }

    // Let the ASM bytecode library perform the actual dataflow analysis.
    Frame[] asmFrames = super.analyze(owner, asmMethod);

    for (int i = 0; i < asmFrames.length; i++) {
      // Convert the ASM stack frames to the representation used in the
      // translator and associate them to the individual bytecode instructions.
      insns.get(map[i]).setFrame(
          convertFrame(asmFrames[i], asmMethod.maxLocals, asmMethod.maxStack));
    }

    return asmFrames;
  }

  /**
   * Computes a mapping from the method instructions in the representation of
   * the ASM bytecode library to the representation used in our translator.
   *
   * @param asmInsns  The list of method instructions as represented in the ASM
   *                  bytecode library.
   *
   * @see #map
   */
  private void computeMap(InsnList asmInsns) {
    map = new int[asmInsns.size()];
    int insnIndex = 0;
    for (int i = 0; i < asmInsns.size(); i++) {
      map[i] = insnIndex;

      AbstractInsnNode asmInsn = asmInsns.get(i);
      // Only increment the instruction index if the InsnNode is a real bytecode
      // instruction.
      if (!(asmInsn instanceof LabelNode)
          && !(asmInsn instanceof FrameNode)
          && !(asmInsn instanceof LineNumberNode)) {
        insnIndex++;
      }
    }
  }

  private boolean isThisInitializer(int asmInsn) {
    Instruction insn =
      method.getInstructions().get(map[asmInsn]).getInstruction();
    if (method.isConstructor() && (insn instanceof InvokeSpecialInstruction)) {
      BCMethod initMethod = ((InvokeSpecialInstruction) insn).getMethod();

      Frame asmInsnFrame = getFrames()[asmInsn];
      Value receiverValue = asmInsnFrame.getStack(
          asmInsnFrame.getStackSize() - (initMethod.getParameterCount() + 1));

      Frame asmFirstFrame = getFrames()[0];
      Value thisValue = asmFirstFrame.getLocal(0);

      return receiverValue == thisValue;
    }
    return false;
  }

  protected void newControlFlowEdge(int asmInsn, int asmSuccessor) {
    // Update the information as of whether the this object has been
    // initialized at the given instruction.
    InstructionHandle insn = method.getInstructions().get(map[asmInsn]);
    InstructionHandle successor =
      method.getInstructions().get(map[asmSuccessor]);
    successor.setThisInitialized(
        insn.isThisInitialized() || isThisInitializer(asmInsn));
  }

  protected boolean newControlFlowExceptionEdge(int asmInsn, int asmSuccessor) {
    // Update the information as of whether the this object has been
    // initialized at the given instruction.
    InstructionHandle insn = method.getInstructions().get(map[asmInsn]);
    InstructionHandle successor =
      method.getInstructions().get(map[asmSuccessor]);
    successor.setThisInitialized(
        insn.isThisInitialized() || isThisInitializer(asmInsn));

    return newControlFlowExceptionEdge(
        method.getInstructions().get(map[asmInsn]),
        method.getInstructions().get(map[asmSuccessor]),
        getFrames()[asmInsn]);
  }

  /**
   * Returns whether the given {@code successor} instruction is an exceptional
   * successor of the {@code insn} instruction.
   *
   * @param insn       The eventual source of the exceptional edge in the
   *                   control flow graph.
   * @param successor  The eventual target of the exceptional edge in the
   *                   control flow graph.
   * @param insnFrame  The JVM frame at the given instruction {@code insn}.
   * @return           Whether the given {@code successor} instruction is an
   *                   exceptional successor of the {@code insn} instruction.
   */
  private boolean newControlFlowExceptionEdge(
      InstructionHandle insn,
      InstructionHandle successor,
      Frame insnFrame) {
    // Check whether any of the exceptions thrown by the instruction insn is
    // caught by an exception handler starting at the successor instruction.
    List<JType> exceptions = computeExceptions(insn, insnFrame);
    for (JType exception : exceptions) {
      // The tightest exception handler type found so far. This is required
      // since exception handlers appearing later on whose handler type is a
      // subtype of this type will never catch the current exception.
      JType tightestHandlerType = JNullType.NULL;
      for (ExceptionHandler handler : activeHandlers[insn.getIndex()]) {
        JType handlerType = handler.getType();
        if (exception.isSubtypeOf(handlerType)) {
          // The exception type is a subtype of the handler's type meaning that
          // no further exception handlers will ever catch this exception at
          // runtime. Therefore, we can return from the method in any case.
          return successor == handler.getHandler();
        } else if (handlerType.isSubtypeOf(exception)
            && tightestHandlerType.isProperSubtypeOf(handlerType)) {
          // The exception type is a supertype of the handler's type, so we may
          // have to go on unless the handler starts at the successor
          // instruction.
          if (handler.getHandler() == successor) {
            return true;
          }
          // Update the tightest exception handler type found so far.
          tightestHandlerType = handlerType;
        }
      }
    }

    // If we are explicitly modeling runtime exceptions implicitly thrown by
    // individual bytecode instructions, we must also check whether any of them
    // are caught by an exception handler starting at the successor instruction.
    // Note that for those runtime exceptions we know the exact runtime type
    // so only exception handlers for supertypes of the runtime exception type
    // are possible candidates.
    if (modelRuntimeExceptions) {
      Instruction instruction = insn.getInstruction();
      for (String runtimeException : instruction.getRuntimeExceptions()) {
        JType exception = TypeLoader.getClassType(runtimeException);
        for (ExceptionHandler handler : activeHandlers[insn.getIndex()]) {
          JType handlerType = handler.getType();
          // We must only check for handler types which are supertypes of the
          // current exception type as we know the exact runtime type of the
          // exception.
          if (exception.isSubtypeOf(handlerType)) {
            return successor == handler.getHandler();
          }
        }
      }
    }

    return false;
  }

  /**
   * Returns the set of exceptions which may be thrown by the given bytecode
   * instruction {@code insn}.
   *
   * @param insn       The bytecode instruction throwing the exceptions.
   * @param insnFrame  The JVM frame at the given bytecode instruction.
   * @return           The set of exceptions which may be thrown by the given
   *                   bytecode instruction {@code insn}.
   */
  private static List<JType> computeExceptions(
      InstructionHandle insn,
      Frame insnFrame) {
    Instruction instruction = insn.getInstruction();
    List<JType> exceptions = new ArrayList<JType>();

    if (instruction.equals(AThrowInstruction.ATHROW)) {
      Value thrownValue = insnFrame.getStack(insnFrame.getStackSize() - 1);
      Type thrownType = ((BasicValue) thrownValue).getType();
      exceptions.add(convertType(thrownType));
    } else if (instruction instanceof InvokeInstruction) {
      BCMethod method = ((InvokeInstruction) instruction).getMethod();
      exceptions.addAll(Arrays.asList(method.getExceptionTypes()));
    }

    return exceptions;
  }

  /**
   * Converts the given {@code asmFrame} as represented by the ASM bytecode
   * library to the representation (an instance of {@code StackFrame}) used by
   * our translator.
   *
   * @param asmFrame   The JVM frame of the ASM bytecode library to convert.
   * @param maxLocals  The maximal number of local variables of the frame.
   * @param maxStack   The maximal number of stack elements of the frame.
   * @return           The converted JVM frame.
   */
  private static StackFrame convertFrame(
      Frame asmFrame,
      int maxLocals,
      int maxStack) {
    if (asmFrame != null) {
      StackFrame frame = new StackFrame(maxLocals, maxStack);
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

  /**
   * Converts the given {@code asmType} as represented by the ASM bytecode
   * library to the representation (an instance of {@code JType}) used by our
   * translator.
   *
   * @param asmType  The type of the ASM bytecode library to convert.
   * @return         The converted type.
   */
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

  /**
   * Specialization of a {@code SimpleVerifier} which uses the class repository
   * of the translator to lookup the type information required during the
   * dataflow analysis.
   *
   * <p>
   * For the computation of the types of the instructions' stack frames during
   * the dataflow analysis, the ASM bytecode library provides the
   * {@code SimpleVerifier} class. Since ASM itself does not maintain a class
   * repository, the {@code SimpleVerifier} provides a set of {@code protected}
   * methods which look up the type information required during the dataflow
   * analysis and which can be overridden by a subclass to look up that
   * information in a class repository which is exactly what we are doing here.
   * </p>
   *
   * @author Ovidio Mallo
   */
  private static final class Verifier extends SimpleVerifier {

    /**
     * Returns whether the given type {@code t} is an interface.
     *
     * @param t  The eventual interface type.
     * @return   Whether the given type {@code t} is an interface.
     */
    protected boolean isInterface(Type t) {
      JType type = convertType(t);
      if (type.isClassType()) {
        return ((JClassType) type).isInterface();
      }
      return false;
    }

    /**
     * Returns the superclass of the given type {@code t}.
     *
     * @param t  The type whose superclass to return.
     * @return   The superclass of the given type {@code t}.
     */
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

    /**
     * Returns whether the type contained in the given {@code value} is a
     * subtype of the type contained {@code expected} value.
     *
     * @param value     The value containing the eventual subtype.
     * @param expected  The value containing the eventual supertype.
     * @return          Whether the type contained in the given {@code value} is
     *                  a subtype of the type contained {@code expected} value.
     */
    protected boolean isSubTypeOf(final Value value, final Value expected) {
      JType subtype = convertType(((BasicValue) value).getType());
      JType supertype = convertType(((BasicValue) expected).getType());
      return subtype.isSubtypeOf(supertype);
    }

    /**
     * Whether the type {@code u} is assignable from the type {@code t}.
     *
     * @param t  The type which may be assignable <i>to</i> the type {@code u}.
     * @param u  The type which may be assignable <i>from</i> the type
     *           {@code t}.
     * @return   Whether the type {@code u} is assignable from the type
     *           {@code u}.
     */
    protected boolean isAssignableFrom(Type t, Type u) {
      JType src = convertType(u);
      JType dst = convertType(t);
      return src.isSubtypeOf(dst);
    }
  }
}
