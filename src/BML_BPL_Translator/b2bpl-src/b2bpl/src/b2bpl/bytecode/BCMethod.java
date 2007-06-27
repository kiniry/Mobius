package b2bpl.bytecode;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import b2bpl.bytecode.analysis.ControlFlowGraph;
import b2bpl.bytecode.bml.ast.BMLAssertStatement;
import b2bpl.bytecode.bml.ast.BMLAssumeStatement;
import b2bpl.bytecode.bml.ast.BMLLoopSpecification;
import b2bpl.bytecode.bml.ast.BMLMethodSpecification;
import b2bpl.bytecode.instructions.Instruction;
import b2bpl.bytecode.instructions.InvokeInstruction;
import b2bpl.translation.ITranslationConstants;


public class BCMethod extends BCMember implements IOpCodes {

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
  
  private Set<String> m = new HashSet<String>(); // potentially modified variables
  private Set<String> a = new HashSet<String>(); // all variables visble to this method
  private Set<String> p = new HashSet<String>(); // propagated variables from invoked methods

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
    
    s.append(name.replace(IConstants.CONSTRUCTOR_NAME, ITranslationConstants.CONSTRUCTOR_NAME));
    
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
  
  
  /**
   * If a class field of a given JType t is being modified in this method,
   * it will appear in this collection.
   * @return List of all potentially modified types
   */
  public String[] getModifiedFields() {
    return this.m.toArray(new String[this.m.size()]);
  }
  
  /**
   * If a class field of a given JType t is accessible from within this method,
   * it will appear in this collection.
   * @return List of all accessible types
   */
  public String[] getModifiableFields() {
    return this.a.toArray(new String[this.a.size()]);
  }
  
  /**
   * If a class field of a given JType t is modified by a method called within this method,
   * it will appear in this collection.
   * @return List of all propagated types
   */
  public String[] getPropagatedFields() {
    if (!this.fetchedPropagatedFields) {
      this.p.clear();
      this.fetchPropagatedFields(this);
    }
    return this.p.toArray(new String[this.p.size()]);
  }
  
  /**
   * Checks whether there are class fields of a given JType t which
   * are being modified in this methd.
   * @param t JType of the class field
   * @return {@code True}, if there is a class field of the given type which is modified in this method.
   * /
  public boolean isModifiedType(String t) {
    return m.contains(t);
  } */
  
  /**
   * Adds a new JType object to the collection of modifies types, indicating
   * that there is a class field in this method's owner class of JType t
   * with is being modified in this method.
   * @param t JType object
   */
  public void addModifiedField(String t) { m.add(t); }
  
  /**
   * Adds a new JType object to the collection of modifiable types, indicating
   * that there is a class field in this method's owner class of JType t
   * which is accessible from within this method.
   * @param t JType object
   */
  public void addModifiableField(String t) { a.add(t); }
  
  public boolean isModifiedField(String t) { return this.m.contains(t); }
  
  public boolean isModifiableField(String t) { return this.a.contains(t); }
  
  public boolean isPropagatedField(String t) { return this.a.contains(t); }
  
  private boolean fetchedPropagatedFields = false;
  /**
   * Automatically retrieves all class fields which are potentially modified
   * by a method invokation from within this method.
   *
   */
  private void fetchPropagatedFields(BCMethod currentMethod) {
    if (currentMethod.getInstructions() == null) return;
    
    for (InstructionHandle ih : currentMethod.getInstructions()) {
      Instruction instr = ih.getInstruction();
      if (instr instanceof InvokeInstruction) {
        
        BCMethod method = ((InvokeInstruction)instr).getMethod();
        this.fetchPropagatedFields(method);
        
        for (String mt : method.getModifiedFields()) {
          currentMethod.p.add(mt);
        }
        for (String pt : method.getPropagatedFields()) {
          currentMethod.p.add(pt);
        }
        
        currentMethod.fetchedPropagatedFields = true;
        
      }
    }

  }
  
}
