package mobius.bico;

import mobius.bico.MethodHandler.MethodNotFoundException;

import org.apache.bcel.Constants;
import org.apache.bcel.classfile.Code;
import org.apache.bcel.classfile.CodeException;
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
import org.apache.bcel.generic.GOTO;
import org.apache.bcel.generic.GOTO_W;
import org.apache.bcel.generic.ICONST;
import org.apache.bcel.generic.IINC;
import org.apache.bcel.generic.IMPDEP1;
import org.apache.bcel.generic.IMPDEP2;
import org.apache.bcel.generic.INSTANCEOF;
import org.apache.bcel.generic.IfInstruction;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.InvokeInstruction;
import org.apache.bcel.generic.JsrInstruction;
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
import org.apache.bcel.generic.Select;
import org.apache.bcel.generic.StackConsumer;
import org.apache.bcel.generic.StackInstruction;
import org.apache.bcel.generic.StackProducer;
import org.apache.bcel.generic.Type;

public class MethodExecutor extends ABasicExecutor {

  /** determine the span of the 'reserved' methods names number default is 1. */
  private static final int RESERVED_METHODS = 1;

  private ClassGen fClass;
  private ConstantPoolGen fConstantPool;
  
  
  public MethodExecutor(ABasicExecutor be, ClassGen cg) {
    super(be);
    
    fClass = cg;
    fConstantPool = cg.getConstantPool();
  }
  
  public void start() throws ClassNotFoundException {
    
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
      
      doMethodSignature(meth, methodName);
    }
    for (Method meth: methods) {
      doMethodInstructions(meth);
    }
  }
  /**
   * write the method signature.
   * 
   * @param method
   *            the method to add
   * @throws ClassNotFoundException
   */
  private void doMethodSignature( Method method,
                                 int coqMethodName) throws ClassNotFoundException {
    // InstructionList il = mg.getInstructionList();
    // InstructionHandle ih[] = il.getInstructionHandles();
    // signature
    
    final int tab = 2;
    final MethodGen mg = new MethodGen(method, fClass.getClassName(), fConstantPool);
    fMethodHandler.addMethod(mg);
    String name = "";
    try {
      name = fMethodHandler.getName(mg);
    } 
    catch (MethodNotFoundException e) {
      e.printStackTrace();
      System.exit(1); // cannot happen
      
    }
    String str = "Definition " + name;
    str += "ShortSignature : ShortMethodSignature := METHODSIGNATURE.Build_t";
    Util.writeln(fOut, tab, str);
    str = "(" + coqMethodName + "%positive)";
    Util.writeln(fOut, tab + 1, str);
    final Type[] atrr = method.getArgumentTypes();
    if (atrr.length == 0) {
      Util.writeln(fOut, tab + 1, "nil");
    } 
    else {
      str = "(";
      for (int i = 0; i < atrr.length; i++) {
        str = str.concat(Util.convertType(atrr[i], fRepos) + "::");
      }
      str = str.concat("nil)");
      Util.writeln(fOut, tab + 1, str);
    }
    final Type t = method.getReturnType();
    Util.writeln(fOut, tab + 1, Util.convertTypeOption(t, fRepos));
    Util.writeln(fOut, tab, ".");
    String clName = "className";
    if (fClass.getJavaClass().isInterface()) {
      clName = "interfaceName";
    }

    str = "Definition " + name + "Signature : MethodSignature := " + "(" + clName + ", " + 
                         name + "ShortSignature).\n";
    Util.writeln(fOut, 2, str);
    fOut.println();
  }
  
  
  /**
   * Write the method body.
   * @throws MethodNotFoundException
   * @throws ClassNotFoundException
   */
  private void doMethodInstructions(Method method) 
    throws ClassNotFoundException {
    final MethodGen mg = new MethodGen(method, fClass.getClassName(), fConstantPool);
    // LocalVariableGen[] aa = mg.getLocalVariables();
    // // aa[i].toString();
    // System.out.println(aa.length);
    // if (aa.length != 0) {System.out.println(aa[0].toString());}
    final int tab = 2;
    String name = "";
    try {
      name = fMethodHandler.getName(mg);
    } 
    catch (MethodNotFoundException e) {
      e.printStackTrace(); // cannot happen
      System.exit(1);
    }
    String str;

    if (!method.isAbstract()) {
      // instructions
      str = "Definition " + name + "Instructions : " + 
            fImplemSpecif.instructionsType() + " :=";

      // System.out.println(str);
      Util.writeln(fOut, tab, str);
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
          Util.writeln(fOut, tab + 1, fImplemSpecif.instructionsCons(str, posPre, pos));
        }
        // special case for the last instruction
        Util.writeln(fOut, tab + 1, fImplemSpecif.instructionsEnd(doInstruction(pos,
                                      listins[listins.length - 1]), pos));
      } 
      else {
        Util.writeln(fOut, tab + 1, fImplemSpecif.getNoInstructions());
      }

      Util.writeln(fOut, tab, ".");
      fOut.println();

      // exception handlers
      final Code code = method.getCode();
      boolean handlers = false;
      if (code != null) {
        final CodeException[] etab = code.getExceptionTable();
        if (etab != null && etab.length > 0) {
          handlers = true;
          str = "Definition " + name + "Handlers : list ExceptionHandler := ";
          Util.writeln(fOut, tab, str);
          for (int i = 0; i < etab.length; i++) {
            str = "(EXCEPTIONHANDLER.Build_t ";
            final int catchType = etab[i].getCatchType();
            if (catchType == 0) {
              str += "None ";
            }
            else {
              str += "(Some ";
              final String exName = method.getConstantPool().getConstantString(catchType,
                                                                  Constants.CONSTANT_Class);
              str += Util.coqify(exName);
              str += ".className) ";
            }
            str += etab[i].getStartPC() + "%N ";
            str += etab[i].getEndPC() + "%N ";
            str += etab[i].getHandlerPC() + "%N)::";
            Util.writeln(fOut, tab + 1, str);
          }
          Util.writeln(fOut, tab + 1, "nil");
          Util.writeln(fOut, 2, ".");
          fOut.println();
        }
      }

      // body
      str = "Definition " + name + "Body : BytecodeMethod := BYTECODEMETHOD.Build_t";
      // System.out.println(str);
      Util.writeln(fOut, tab, str);
      fImplemSpecif.printExtraBodyField(fOut);

      Util.writeln(fOut, tab + 1, name + "Instructions");
      // exception names not handlers now
      // TODO: Handle handlers for map....
      if (handlers) {
        Util.writeln(fOut, tab + 1, name + "Handlers");
      } 
      else {
        Util.writeln(fOut, tab + 1, "nil");
      }
      Util.writeln(fOut, tab + 1, "" + mg.getMaxLocals());
      Util.writeln(fOut, tab + 1, "" + mg.getMaxStack());
      Util.writeln(fOut, tab, ".");
      fOut.println();
    }

    // method
    str = "Definition " + name + "Method : Method := METHOD.Build_t";
    // System.out.println(str);
    Util.writeln(fOut, tab, str);
    Util.writeln(fOut, tab + 1, name + "ShortSignature");
    if (method.isAbstract()) {
      str = "None";
    } 
    else {
      str = "(Some " + name + "Body)";
    }
    Util.writeln(fOut, tab + 1, str);
    Util.writeln(fOut, tab + 1, "" + method.isFinal());
    Util.writeln(fOut, tab + 1, "" + method.isStatic());
    Util.writeln(fOut, tab + 1, "" + method.isNative());
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
      // String attr="0x"+Integer.toHexString(method.getAccessFlags());
      // System.out.println("Unknown modifier of method "+name+" :
      // "+attr);
      str = "Package"; // " (* "+attr+" *)"
    }
    Util.writeln(fOut, tab + 1, str);
    // System.out.println();System.out.println();
    Util.writeln(fOut, tab, ".");
    fOut.println();
  }
  
  
  /**
   * Handles one instruction ins at position pos.
   * 
   * @param ins
   *            instruction to translate
   * @return "(ins)" in Coq syntax
   * @throws ClassNotFoundException
   * @throws MethodNotFoundException
   */
  private String doInstruction(int pos, Instruction ins) throws ClassNotFoundException {
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
      final String index = Util.printZ(((BranchInstruction) ins).getIndex());

      if (ins instanceof GOTO) {
        ret = name + " " + index;
      } 
      else if (ins instanceof GOTO_W) {
        ret = "Goto " + index;
      } 
      else if (ins instanceof IfInstruction) {
        String op;

        if (name.endsWith("null")) {
          // ifnonnull o --> Ifnull NeRef o
          // ifnull o --> Ifnull EqRef o
          if (name.indexOf("non") != -1) {
            op = "Ne";
          } 
          else {
            op = "Eq";
          }
          ret = "Ifnull " + op + "Ref " + index;
        } 
        else if (name.charAt(2) != '_') {
          // Ifgt -> GtInt
          op = Util.upCase(name.substring(2));
          ret = "If0 " + op + "Int " + index;
        } 
        else {
          op = Util.upCase(name.substring(7));
          if (name.charAt(3) == 'i') {
            ret = "If_icmp " + op + "Int " + index;
          } 
          else {
            ret = "If_acmp " + op + "Ref " + index;
          }
        }
      } 
      else if (ins instanceof JsrInstruction) {
        ret = Util.unhandled("JsrInstruction", ins);
      } 
      else if (ins instanceof Select) {
        // TODO: Select
        ret = Util.unimplemented("Select", ins);
      } 
      else {
        ret = Util.unknown("BranchInstruction", ins);
      }
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
          final String fs = className + "." + Util.coqify(fom.getName(fConstantPool)) + "FieldSignature";
          ret = name + " " + fs;
        } 
        else if (ins instanceof InvokeInstruction) {
          String ms;
          try {
            ms = className + "." + fMethodHandler.getName((InvokeInstruction) fom, fConstantPool) + 
                         "Signature";
          } 
          catch (MethodNotFoundException e) {
            System.err.println("warning : doInstruction: " + 
                               fom.getReferenceType(fConstantPool).toString() + "." + 
                               fom.getName(fConstantPool) + " (" + e.getMessage() + ")" +
                                  " was supposed to be loaded before use...");
            ms = className + "." + Util.coqify(fom.getName(fConstantPool)) + "Signature";
          }
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
        ret = name + " " + Util.coqify(((NEW) ins).getType(fConstantPool).toString()) + ".className";
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
}
