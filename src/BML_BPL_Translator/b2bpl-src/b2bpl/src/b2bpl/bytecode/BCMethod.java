package b2bpl.bytecode;

import java.util.List;

import b2bpl.bytecode.analysis.ControlFlowGraph;
import b2bpl.bytecode.bml.ast.BMLAssertStatement;
import b2bpl.bytecode.bml.ast.BMLAssumeStatement;
import b2bpl.bytecode.bml.ast.BMLLoopSpecification;
import b2bpl.bytecode.bml.ast.BMLMethodSpecification;
import b2bpl.translation.TranslationConstants;


public class BCMethod extends BCMember {

  public static final BCMethod[] EMPTY_ARRAY = new BCMethod[0];

  private final String name;

  private final JType returnType;

  private final JType[] parameterTypes;

  private final JClassType[] exceptionTypes;

  private JType[] realParameterTypes;

  private final String descriptor;

  private BMLMethodSpecification specification;

  private Instructions instructions;

  private int maxStack = -1;

  private int maxLocals = -1;

  private ExceptionHandler[] exceptionHandlers;

  private ControlFlowGraph cfg;

  public BCMethod(
      int accessModifiers,
      JClassType owner,
      String name,
      JType returnType,
      JType[] parameterTypes,
      JClassType[] exceptionTypes) {
    super(accessModifiers, owner);
    this.name = name;
    this.returnType = returnType;
    this.parameterTypes = parameterTypes;
    this.exceptionTypes = exceptionTypes;
    this.descriptor = JType.computeMethodDescriptor(returnType, parameterTypes);
  }

  public String getName() {
    return name;
  }

  public JType getReturnType() {
    return returnType;
  }

  public JType[] getParameterTypes() {
    return parameterTypes;
  }

  public JClassType[] getExceptionTypes() {
    return exceptionTypes;
  }

  public JType[] getRealParameterTypes() {
    if (realParameterTypes == null) {
      if (isStatic()) {
        realParameterTypes = parameterTypes;
      } else {
        realParameterTypes = new JType[parameterTypes.length + 1];
        realParameterTypes[0] = owner;
        System.arraycopy(
            parameterTypes,
            0,
            realParameterTypes,
            1,
            parameterTypes.length);
      }
    }
    return realParameterTypes;
  }

  public String getDescriptor() {
    return descriptor;
  }

  public String getQualifiedName() {
    return owner.getName() + "." + name;
  }
  
  public String getQualifiedBoogiePLName() {
    StringBuffer s = new StringBuffer();
    s.append(owner.getName());
    s.append('.');
    
    s.append(name.replace(Constants.CONSTRUCTOR_NAME, TranslationConstants.CONSTRUCTOR_NAME));
    
    if (this.returnType.getName() != "void") {
      s.append('.');
      s.append(this.returnType.toString());
    }
    
    return s.toString();
  }

  public BMLMethodSpecification getSpecification() {
    return specification;
  }

  public void setSpecification(BMLMethodSpecification specification) {
    this.specification = specification;
  }

  public Instructions getInstructions() {
    return instructions;
  }

  public int getMaxStack() {
    return maxStack;
  }

  public int getMaxLocals() {
    return maxLocals;
  }

  public ExceptionHandler[] getExceptionHandlers() {
    return exceptionHandlers;
  }

  void setCodeInfo(
      Instructions instructions,
      int maxStack,
      int maxLocals,
      ExceptionHandler[] exceptionHandlers) {
    this.instructions = instructions;
    this.maxStack = maxStack;
    this.maxLocals = maxLocals;
    this.exceptionHandlers = exceptionHandlers;
  }

  public boolean isConstructor() {
    return CONSTRUCTOR_NAME.equals(name);
  }

  public boolean isClassInitializer() {
    return CLASS_INITIALIZER_NAME.equals(name);
  }

  public boolean isVoid() {
    return returnType == JBaseType.VOID;
  }

  public int getParameterCount() {
    return parameterTypes.length;
  }

  public boolean isAbstract() {
    return (accessModifiers & ACC_ABSTRACT) != 0;
  }

  public boolean isNative() {
    return (accessModifiers & ACC_NATIVE) != 0;
  }

  public boolean isSynchronized() {
    return (accessModifiers & ACC_SYNCHRONIZED) != 0;
  }

  public List<BCMethod> getOverrides() {
    return owner.getMethodOverrides(name, descriptor);
  }

  public ControlFlowGraph getCFG() {
    return cfg;
  }

  public void setCFG(ControlFlowGraph cfg) {
    this.cfg = cfg;
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append(returnType.getName());
    sb.append(' ');
    sb.append(name);
    sb.append('(');
    for (int i = 0; i < parameterTypes.length; i++) {
      if (i > 0) {
        sb.append(", ");
      }
      sb.append(parameterTypes[i]);
    }
    sb.append(')');

    if (exceptionTypes.length > 0) {
      sb.append(" throws ");
      for (int i = 0; i < exceptionTypes.length; i++) {
        if (i > 0) {
          sb.append(", ");
        }
        sb.append(exceptionTypes[i].getName());
      }
    }
    sb.append(System.getProperty("line.separator"));

    if (specification != null) {
      sb.append(specification.toString());
    }

    if (instructions != null) {
      sb.append("  ");
      sb.append("maxStack: " + maxStack + ", maxLocals: " + maxLocals);

      sb.append(System.getProperty("line.separator"));
      for (InstructionHandle insn : instructions) {
        for (BMLAssertStatement assertion : insn.getAssertions()) {
          sb.append(assertion);
          sb.append(System.getProperty("line.separator"));
        }
        for (BMLAssumeStatement assumption : insn.getAssumptions()) {
          sb.append(assumption);
          sb.append(System.getProperty("line.separator"));
        }
        for (BMLLoopSpecification loopSpec : insn.getLoopSpecifications()) {
          sb.append(loopSpec);
          sb.append(System.getProperty("line.separator"));
        }
        sb.append("  ");
        sb.append(insn.toString());
        sb.append(System.getProperty("line.separator"));
      }

      for (ExceptionHandler handler : exceptionHandlers) {
        sb.append(handler);
        sb.append(System.getProperty("line.separator"));
      }
    }

    return sb.toString();
  }
}
