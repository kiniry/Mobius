package mobius.bico.executors;

import mobius.bico.Util;
import mobius.bico.bicolano.coq.CType;
import mobius.bico.bicolano.coq.CoqStream;
import mobius.bico.bicolano.coq.Translator;
import mobius.bico.bicolano.coq.Translator.Access;
import mobius.bico.implem.IImplemSpecifics;
import mobius.bico.visitors.InstructionVisitor;

import org.apache.bcel.Constants;
import org.apache.bcel.classfile.Code;
import org.apache.bcel.classfile.CodeException;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.MethodGen;
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

  /** the main output stream of the executor. */
  private final CoqStream fOut;
  
  /** the implementation specific library. */
  private final IImplemSpecifics fImplemSpecif;
  
  /**
   * The constructor.
   * @param be the BasicExecutor to get the initialization from
   * @param cg the current class
   */
  public MethodExecutor(final ASignatureExecutor be, final ClassGen cg) {
    super(be);
    fClass = cg;
    fConstantPool = cg.getConstantPool();
    fOut = getOut();
    fImplemSpecif = getImplemSpecif();
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
      final String name = getMethodHandler().getName(mg);
     
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
        str2 += fImplemSpecif.methodsCons(getMethodHandler().getName(imeth[i]));
      }
      str2 += fImplemSpecif.methodsEnd(getMethodHandler().getName(imeth[imeth.length - 1]));
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
    
    fOutSig.definitionStart(name + "Short", "ShortMethodSignature");
    fOutSig.incPrintln("METHODSIGNATURE.Build_t");
    fOutSig.println("(" + coqMethodName + "%positive)");
    final Type[] atrr = method.getArgumentTypes();
    if (atrr.length == 0) {
      fOutSig.println("nil");
    } 
    else {
      String str = "(";
      for (int i = 0; i < atrr.length; i++) {
        str = str.concat(CType.getInstance().convertType(atrr[i], getRepository()) + "::");
      }
      str = str.concat("nil)");
      fOutSig.println(str);
    }
    final Type t = method.getReturnType();
    fOutSig.println(Util.convertTypeOption(t, getRepository()));
    fOutSig.decPrintln(".");
  

    fOutSig.definition(name, "MethodSignature", 
                       Translator.couple("name", name + "Short"));
    fOutSig.println();
  }
  
  
  /**
   * Write the method definition.
   * @param method the method to treat
   * @param name the name of the method
   * @throws ClassNotFoundException if a class name cannot be resolved
   */
  private void doMethod(final Method method, final String name) throws ClassNotFoundException {
    
    // method
    String str = "Definition " + name + " : Method := METHOD.Build_t";
    // System.out.println(str);
    fOut.println(str);
    fOut.incTab();
    fOut.println(name + "Short");
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
    fOut.println(Access.translate(method));
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
      il.setPositions();
      InstructionHandle ih = il.getInstructionHandles()[0];
      
      int pos = 0;
      String paren = "";
      while (ih.getNext() != null) {
        paren += ")";
        str = doInstruction(pos, ih.getInstruction());
        final int posPre = ih.getPosition();
        pos = ih.getNext().getPosition();
        fOut.println(fImplemSpecif.instructionsCons(str, posPre, pos));
        ih = ih.getNext();
      }
      // special case for the last instruction
      fOut.println(fImplemSpecif.instructionsEnd(doInstruction(pos,
                                    ih.getInstruction()), pos));
      
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
            str += Util.coqify(exName) + "Type.name) ";
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
    final String ret = InstructionVisitor.translate(getMethodHandler(), fConstantPool, ins,
                                                    getRepository());
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
      getMethodHandler().addMethod(mg);
      getDico().addMethod(getMethodHandler().getName(mg), 
                      getDico().getCoqPackageName(fClass.getJavaClass()),
                      getDico().getCoqClassName(fClass.getJavaClass()),
                      methodName);

      final String name = getMethodHandler().getName(mg);
      doMethodSignature(meth, methodName, name);
    }
    
  }
}
