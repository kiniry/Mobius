package mobius.bico;

import mobius.bico.visitors.BranchInstructionVisitor;

import org.apache.bcel.Constants;
import org.apache.bcel.classfile.Code;
import org.apache.bcel.classfile.CodeException;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ACONST_NULL;
import org.apache.bcel.generic.ANEWARRAY;
import org.apache.bcel.generic.ARRAYLENGTH;
import org.apache.bcel.generic.ATHROW;
import org.apache.bcel.generic.ArithmeticInstruction;
import org.apache.bcel.generic.ArrayInstruction;
import org.apache.bcel.generic.BIPUSH;
import org.apache.bcel.generic.BREAKPOINT;
import org.apache.bcel.generic.BasicType;
import org.apache.bcel.generic.BranchInstruction;
import org.apache.bcel.generic.CHECKCAST;
import org.apache.bcel.generic.CPInstruction;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.ConversionInstruction;
import org.apache.bcel.generic.DCMPG;
import org.apache.bcel.generic.DCMPL;
import org.apache.bcel.generic.DCONST;
import org.apache.bcel.generic.FCMPG;
import org.apache.bcel.generic.FCMPL;
import org.apache.bcel.generic.FCONST;
import org.apache.bcel.generic.FieldInstruction;
import org.apache.bcel.generic.FieldOrMethod;
import org.apache.bcel.generic.ICONST;
import org.apache.bcel.generic.IINC;
import org.apache.bcel.generic.IMPDEP1;
import org.apache.bcel.generic.IMPDEP2;
import org.apache.bcel.generic.INSTANCEOF;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.InvokeInstruction;
import org.apache.bcel.generic.LCMP;
import org.apache.bcel.generic.LCONST;
import org.apache.bcel.generic.LDC;
import org.apache.bcel.generic.LDC2_W;
import org.apache.bcel.generic.LocalVariableInstruction;
import org.apache.bcel.generic.MONITORENTER;
import org.apache.bcel.generic.MONITOREXIT;
import org.apache.bcel.generic.MULTIANEWARRAY;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.NEW;
import org.apache.bcel.generic.NEWARRAY;
import org.apache.bcel.generic.NOP;
import org.apache.bcel.generic.RET;
import org.apache.bcel.generic.ReferenceType;
import org.apache.bcel.generic.ReturnInstruction;
import org.apache.bcel.generic.SIPUSH;
import org.apache.bcel.generic.StackConsumer;
import org.apache.bcel.generic.StackInstruction;
import org.apache.bcel.generic.StackProducer;
import org.apache.bcel.generic.Type;

/**
 * This class is used in the treatment of methods by bico.
 * 
 * @author J. Charles (julien.charles@inria.fr), 
 * P. Czarnik (czarnik@mimuw.edu.pl), 
 * L. Hubert (laurent.hubert@irisa.fr)
 */
class MethodExecutor extends ASignatureExecutor {

  
  
  /** determine the span of the 'reserved' methods names number default is 1. */
  private static final int RESERVED_METHODS = 1;
  
  
  /** the current class to get the method from. */
  private ClassGen fClass;
  
  /** the constant pool corresponding to the class. */
  private ConstantPoolGen fConstantPool;
  
  /**
   * The constructor.
   * @param be the BasicExecutor to get the initialization from
   * @param cg the current class
   */
  public MethodExecutor(final ASignatureExecutor be, final ClassGen cg) {
    super(be);
    fClass = cg;
    fConstantPool = cg.getConstantPool();
  }
  
  /**
   * Starts the generation of the method definitions for Coq.
   * @throws ClassNotFoundException if a class found as a type cannot
   * be resolved
   */
  @Override
  public void start() throws ClassNotFoundException {
    
    final Method[] methods = fClass.getMethods();
    
    for (Method meth: methods) {
      final MethodGen mg = new MethodGen(meth, fClass.getClassName(), fConstantPool);
      final String name = fMethodHandler.getName(mg);
     
      if (!meth.isAbstract()) {
        doInstructions(mg, name);
        final boolean handlers = doExceptionHandlers(meth, name);
        doBody(mg, name, handlers);
      }
      doMethod(meth, name);
    }
  }
  
  /**
   * Write all the method names as an enumeration.
   */
  public void doEnumeration() {
    final JavaClass jc = fClass.getJavaClass();
    // methods
    final Method[] imeth = jc.getMethods();
    if (imeth.length == 0) {
      fOut.println(fImplemSpecif.getNoMethods());
    } 
    else {
      String str2 = "(";
      for (int i = 0; i < imeth.length - 1; i++) {
        str2 += fImplemSpecif.methodsCons(fMethodHandler.getName(imeth[i]) + "Method");
       
      }
      str2 += fImplemSpecif.methodsEnd(Util.coqify(imeth[imeth.length - 1].getName()) +
                                       "Method");
      str2 += ")";
      fOut.println(str2);
    }
  }
  
  /**
   * Write the method signature.
   * 
   * @param method the method to add
   * @param coqMethodName the number representing the method
   * @param name the name of the method
   * @throws ClassNotFoundException if a class name cannot be resolved
   */
  private void doMethodSignature(final Method method,
                                 final int coqMethodName, 
                                 final String name) throws ClassNotFoundException {
    
    String str = "Definition " + name;
    str += "ShortSignature : ShortMethodSignature := METHODSIGNATURE.Build_t";
    fOutSig.incPrintln(str);
    str = "(" + coqMethodName + "%positive)";
    fOutSig.println(str);
    final Type[] atrr = method.getArgumentTypes();
    if (atrr.length == 0) {
      fOutSig.println("nil");
    } 
    else {
      str = "(";
      for (int i = 0; i < atrr.length; i++) {
        str = str.concat(Util.convertType(atrr[i], fRepos) + "::");
      }
      str = str.concat("nil)");
      fOutSig.println(str);
    }
    final Type t = method.getReturnType();
    fOutSig.println(Util.convertTypeOption(t, fRepos));
    fOutSig.decPrintln(".");
    
    String clName = "className";
    if (fClass.getJavaClass().isInterface()) {
      clName = "interfaceName";
    }

    str = "Definition " + name + "Signature : MethodSignature := " + 
                   "(" + clName + ", " + name + "ShortSignature).\n\n";
    fOutSig.println(str);
  }
  
  
  /**
   * Write the method definition.
   * @param method the method to treat
   * @param name the name of the method
   * @throws ClassNotFoundException if a class name cannot be resolved
   */
  private void doMethod(final Method method, final String name) throws ClassNotFoundException {
    
    // method
    String str = "Definition " + name + "Method : Method := METHOD.Build_t";
    // System.out.println(str);
    fOut.println(str);
    fOut.incTab();
    fOut.println(name + "ShortSignature");
    if (method.isAbstract()) {
      str = "None";
    } 
    else {
      str = "(Some " + name + "Body)";
    }
    fOut.println(str);
    fOut.println("" + method.isFinal());
    fOut.println("" + method.isStatic());
    fOut.println("" + method.isNative());
    if (method.isPrivate()) {
      str = "Private";
    } 
    else if (method.isProtected()) {
      str = "Protected";
    } 
    else if (method.isPublic()) {
      str = "Public";
    } 
    else {
      str = "Package"; // " (* "+attr+" *)"
    }
    fOut.println(str);
    fOut.decTab();
    fOut.println(".\n");
    fOut.println();
  }

  /**
   * Write the instructions of a method.
   * @param mg the method.
   * @param name the name of the method
   * @throws ClassNotFoundException in case a type cannot be resolved
   */
  private void doInstructions(final MethodGen mg, 
                              final String name) throws ClassNotFoundException {
    String str = "Definition " + name + "Instructions : " + 
          fImplemSpecif.instructionsType() + " :=";

    // System.out.println(str);
    fOut.println(str);
    fOut.incTab();
    final InstructionList il = mg.getInstructionList();
    if (il != null) {
      final Instruction[] listins = il.getInstructions();
      int pos = 0;
      String paren = "";
      for (int i = 0; i < listins.length - 1; i++) {
        paren += ")";
        str = doInstruction(pos, listins[i]);
        final int posPre = pos;
        pos = pos + listins[i].getLength();
        fOut.println(fImplemSpecif.instructionsCons(str, posPre, pos));
      }
      // special case for the last instruction
      fOut.println(fImplemSpecif.instructionsEnd(doInstruction(pos,
                                    listins[listins.length - 1]), pos));
    } 
    else {
      fOut.println(fImplemSpecif.getNoInstructions());
    }
    fOut.decTab();
    fOut.println(".\n");
  }

  /**
   * Generate the code for the method body.
   * @param mg the method concern
   * @param name the name of the method
   * @param handlers if it has handlers or not
   */
  private void doBody(final MethodGen mg, final String name, final boolean handlers) {
    String str;
    // body
    str = "Definition " + name + "Body : BytecodeMethod := BYTECODEMETHOD.Build_t";
    // System.out.println(str);
    fOut.println(str);
    fOut.incTab();
    fImplemSpecif.printExtraBodyField(fOut);

    fOut.println(name + "Instructions");
    // exception names not handlers now
    // TODO: Handle handlers for map....
    if (handlers) {
      fOut.println(name + "Handlers");
    } 
    else {
      fOut.println("nil");
    }
    fOut.println("" + mg.getMaxLocals());
    fOut.println("" + mg.getMaxStack());
    fOut.decTab();
    fOut.println(".");
    fOut.println();
  }

  /**
   * Treat the exception handlers.
   * @param method the method to treat
   * @param name the name of the method
   * @return <code>true</code> if there was a handler already present
   */
  private boolean doExceptionHandlers(final Method method, final String name) {
   
    // exception handlers
    final Code code = method.getCode();
    boolean handlers = false;
    if (code != null) {
      final CodeException[] etab = code.getExceptionTable();
      if (etab != null && etab.length > 0) {
        handlers = true;
        String str = "Definition " + name + "Handlers : list ExceptionHandler := ";
        fOut.incPrintln(str);
        for (CodeException codExc: etab) {
          str = "(EXCEPTIONHANDLER.Build_t ";
          final int catchType = codExc.getCatchType();
          if (catchType == 0) {
            str += "None ";
          }
          else {
            str += "(Some ";
            final String exName = method.getConstantPool().getConstantString(catchType,
                                                                Constants.CONSTANT_Class);
            str += Util.coqify(exName) + ".className) ";
          }
          str += codExc.getStartPC() + "%N " + 
                 codExc.getEndPC() + "%N " + 
                 codExc.getHandlerPC() + "%N)::";
          fOut.println(str);
        }
        fOut.println("nil");
        fOut.decPrintln(".\n");
      }
    }
    return handlers;
  }
  
  
  /**
   * Handles one instruction ins at position pos.
   * @param pos the position of the instruction
   * @param ins instruction to translate
   * @return "(ins)" in Coq syntax
   * @throws ClassNotFoundException if a class name cannot be resolved
   */
  private String doInstruction(final int pos, 
                               final Instruction ins) throws ClassNotFoundException {
    String ret;

    String name = ins.getName();
    // capitalize name
    if (name != null && name.length() > 0) {
      name = Util.upCase(name);
    } 
    else {
      System.out.println("Empty instruction name?");
      name = "Nop";
    }

    if (ins instanceof ACONST_NULL) {
      ret = name;
    }
    else if (ins instanceof ArithmeticInstruction) {
      final char c = name.charAt(0);

      if (c == 'I') {
        // e.g. Isub -> Ibinop SubInt
        ret = "Ibinop " + Util.upCase(name.substring(1)) + "Int";
      } 
      else if (c == 'D' || c == 'F' || c == 'L') {
        ret = Util.unhandled("ArithmeticInstruction", ins);
      } 
      else {
        ret = Util.unknown("ArithmeticInstruction", ins);
      }
    } 
    else if (ins instanceof ArrayInstruction) {
      final char c = name.charAt(0);

      if (c == 'A' || c == 'B' || c == 'I' || c == 'S') {
        ret = "V";
        if (ins instanceof StackProducer) { // ?aload instructions
          ret += name.substring(1, 6);
        } 
        else if (ins instanceof StackConsumer) { // ?astore
          // instructions
          ret += name.substring(1, 7);
        }
        ret += " " + c + "array";
      } 
      else if (c == 'C' || c == 'D' || c == 'F' || c == 'L') {
        ret = Util.unhandled("ArrayInstruction", ins);
      } 
      else {
        ret = Util.unknown("ArrayInstruction", ins);
      }
    } 
    else if (ins instanceof ARRAYLENGTH) {
      ret = name;
    }
    else if (ins instanceof ATHROW) {
      ret = name;
    }
    else if (ins instanceof BIPUSH) {
      ret = "Const BYTE " + Util.printZ(((BIPUSH) ins).getValue());
    } 
    else if (ins instanceof BranchInstruction) {
      ret = BranchInstructionVisitor.translate((BranchInstruction) ins);
    } 
    else if (ins instanceof BREAKPOINT) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof ConversionInstruction) {
      switch (ins.getOpcode()) {
        case Constants.I2B:
        case Constants.I2S:
          ret = name;
        default:
          ret = Util.unhandled(ins);
      }
    } 
    else if (ins instanceof CPInstruction) {
      final Type type = ((CPInstruction) ins).getType(fConstantPool);
      if (ins instanceof ANEWARRAY) {
        ret = "Newarray " + Util.convertType(type, fRepos);
      } 
      else if (ins instanceof CHECKCAST) {
        ret = name + " " + Util.convertReferenceType((ReferenceType) type, fRepos);
      } 
      else if (ins instanceof FieldOrMethod) {
        final FieldOrMethod fom = (FieldOrMethod) ins;
        final String className = Util.coqify(fom.getReferenceType(fConstantPool).toString());
        // String fmName = coqify(fom.getName(cpg));
        if (ins instanceof FieldInstruction) {
          final String fs = className + "Signature." + 
              Util.coqify(fom.getName(fConstantPool)) + "FieldSignature";
          ret = name + " " + fs;
        } 
        else if (ins instanceof InvokeInstruction) {
          String ms;
          ms = className + "Signature" + "." + 
               fMethodHandler.getName((InvokeInstruction) fom, fConstantPool) + 
               "Signature";

          ret = name + " " + ms;
        } 
        else {
          ret = Util.unknown("FieldOrMethod", ins);
        }
      } 
      else if (ins instanceof INSTANCEOF) {
        ret = name + " " + Util.convertReferenceType((ReferenceType) type, fRepos);
      } 
      else if (ins instanceof LDC) {
        ret = Util.unhandled(ins);
      } 
      else if (ins instanceof LDC2_W) {
        ret = Util.unhandled(ins);
      } 
      else if (ins instanceof MULTIANEWARRAY) {
        ret = Util.unhandled(ins);
      } 
      else if (ins instanceof NEW) {
        ret = name + " " + 
             Util.coqify(((NEW) ins).getType(fConstantPool).toString()) + 
               ".className";
        // convertType(type);
      } 
      else {
        ret = Util.unknown("CPInstruction", ins);
      }
    } 
    else if (ins instanceof DCMPG) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof DCMPL) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof DCONST) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof FCMPG) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof FCMPL) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof FCONST) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof ICONST) {
      ret = "Const INT " + Util.printZ(((ICONST) ins).getValue());
    } 
    else if (ins instanceof IMPDEP1) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof IMPDEP2) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof LCMP) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof LCONST) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof LocalVariableInstruction) {
      final int index = ((LocalVariableInstruction) ins).getIndex();

      if (ins instanceof IINC) {
        ret = name + " " + index + "%N " + Util.printZ(((IINC) ins).getIncrement());
      } 
      else {
        final char c = name.charAt(0);

        if (c == 'A' || c == 'I') {
          // Aload_0 -> Aload
          final int under = name.lastIndexOf('_');
          if (under != -1) {
            name = name.substring(0, under);
          }
          // Aload -> Vload Aval
          ret = "V" + name.substring(1) + " " + c + "val " + index + "%N";
        } 
        else if (c == 'D' || c == 'F' || c == 'L') {
          ret = Util.unhandled("LocalVariableInstruction", ins);
        } 
        else {
          ret = Util.unknown("LocalVariableInstruction", ins);
        }
      }
    } 
    else if (ins instanceof MONITORENTER) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof MONITOREXIT) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof NEWARRAY) {
      final String type = Util.convertType(BasicType.getType(((NEWARRAY) ins)
                                                  .getTypecode()), null);
      ret = name + " " + type;
    } 
    else if (ins instanceof NOP) {
      ret = name;
    }
    else if (ins instanceof RET) {
      ret = Util.unhandled(ins);
    } 
    else if (ins instanceof ReturnInstruction) {
      final char c = name.charAt(0);
      if (c == 'R') { // return nothing
        ret = name;
      } 
      else if (c == 'A' || c == 'I') {
        // Areturn -> Vreturn Aval
        // Ireturn -> Vreturn Ival
        ret = "Vreturn " + c + "val";
      } 
      else if (c == 'D' || c == 'F' || c == 'L') {
        ret = Util.unhandled("ReturnInstruction", ins);
      } 
      else {
        ret = Util.unknown("ReturnInstruction", ins);
      }
    } 
    else if (ins instanceof SIPUSH) {
      ret = "Const SHORT " + Util.printZ(((SIPUSH) ins).getValue());
    } 
    else if (ins instanceof StackInstruction) {
      ret = name;
    } 
    else {
      ret = Util.unknown("Instruction", ins);
    }
    return "(" + ret + ")";

  }


  /**
   * Trigger the writing of the signature of the methods.
   * @throws ClassNotFoundException if there is a type which cannot be
   * properly resolved.
   */
  @Override
  public void doSignature() throws ClassNotFoundException {
    final Method[] methods = fClass.getMethods();
    int methodName = RESERVED_METHODS;
    for (Method meth: methods) {
      methodName++;
      final MethodGen mg = new MethodGen(meth, fClass.getClassName(), 
                                         fConstantPool);
      fDico.addMethod(mg.getClassName() + "." + mg.getName(), 
                      fDico.getCoqPackageName(fClass.getJavaClass()),
                      fDico.getCoqClassName(fClass.getJavaClass()),
                      methodName);
      fMethodHandler.addMethod(mg);
      final String name = fMethodHandler.getName(mg);
      doMethodSignature(meth, methodName, name);
    }
    
  }
}
