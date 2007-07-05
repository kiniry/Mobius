package mobius.bico.visitors;

import mobius.bico.Util;
import mobius.bico.dico.MethodHandler;

import org.apache.bcel.Constants;
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
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.ConversionInstruction;
import org.apache.bcel.generic.DCMPG;
import org.apache.bcel.generic.DCMPL;
import org.apache.bcel.generic.DCONST;
import org.apache.bcel.generic.EmptyVisitor;
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
import org.apache.bcel.generic.InvokeInstruction;
import org.apache.bcel.generic.LCMP;
import org.apache.bcel.generic.LCONST;
import org.apache.bcel.generic.LDC;
import org.apache.bcel.generic.LDC2_W;
import org.apache.bcel.generic.LocalVariableInstruction;
import org.apache.bcel.generic.MONITORENTER;
import org.apache.bcel.generic.MONITOREXIT;
import org.apache.bcel.generic.MULTIANEWARRAY;
import org.apache.bcel.generic.NEW;
import org.apache.bcel.generic.NEWARRAY;
import org.apache.bcel.generic.NOP;
import org.apache.bcel.generic.RET;
import org.apache.bcel.generic.ReferenceType;
import org.apache.bcel.generic.ReturnInstruction;
import org.apache.bcel.generic.SIPUSH;
import org.apache.bcel.generic.StackInstruction;
import org.apache.bcel.generic.Type;
import org.apache.bcel.util.Repository;
import org.apache.bcel.util.SyntheticRepository;


/**
 * Translate the instructions to bicolano friendly versions.
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class InstructionVisitor extends EmptyVisitor {
  /** the result string. */
  private String fRes;
  
  /** the constant pool associated with the visited instructions. */
  private final ConstantPoolGen fConstantPool;

  /** a data structure to stock methods signatures. */
  private final MethodHandler fMethodHandler;
  
  
  /**
   * Construct a new visitor.
   * @param methodHandler the coq method names
   * @param constantPool the constant pool associated with
   * these instructions
   */
  private InstructionVisitor(final MethodHandler methodHandler,
                             final ConstantPoolGen constantPool) {
    fConstantPool = constantPool;
    fMethodHandler = methodHandler;
    fRes = "";
  }
  
  
  /**
   * Set the result to <code>Aconst_null</code>.
   * @param ins ignored
   */
  @Override
  public void visitACONST_NULL(final ACONST_NULL ins) {
    fRes = "Aconst_null";
  }
  
  
  @Override
  public void visitArithmeticInstruction(final ArithmeticInstruction ins) {
    final String name = Util.upCase(ins.getName());
    final char c = name.charAt(0);

    if (c == 'I') {
      // e.g. Isub -> Ibinop SubInt
      fRes = "Ibinop " + Util.upCase(name.substring(1)) + "Int";
    } 
    else if (c == 'D' || c == 'F' || c == 'L') {
      fRes = Util.unhandled("ArithmeticInstruction", ins);
    } 
    else {
      fRes = Util.unknown("ArithmeticInstruction", ins);
    }    
  }
  
  /**
   * Visits an ArrayInstruction using the {@link ArrayInstructionVisitor}
   * and sets the result in consequence.
   * @param ins the instruction which is passed to the called
   * visitor
   */
  @Override
  public void visitArrayInstruction(final ArrayInstruction ins) {
    fRes = ArrayInstructionVisitor.translate((ArrayInstruction) ins);
  }
  
  /**
   * Set the result to <code>Arraylength</code>.
   * @param ins ignored
   */
  @Override
  public void visitARRAYLENGTH(final ARRAYLENGTH ins) {
    fRes = "Arraylength";
  }
  
  /**
   * Set the result to <code>Athrow</code>.
   * @param ins ignored
   */
  @Override
  public void visitATHROW(final ATHROW ins) {
    fRes = "Athrow";
  }
  
  /**
   * Set the result to <code>Const BYTE num</code>.
   * @param ins parameter from where the number is taken
   */
  @Override
  public void visitBIPUSH(final BIPUSH ins) {
    fRes = "Const BYTE " + Util.printZ(((BIPUSH) ins).getValue());
  }
  
  /**
   * Visits a BranchInstruction using the {@link BranchInstructionVisitor}
   * and sets the result in consequence.
   * @param ins the instruction which is passed to the called
   * visitor
   */
  @Override
  public void visitBranchInstruction(final BranchInstruction ins) {
    fRes = BranchInstructionVisitor.translate((BranchInstruction) ins);
  }
  
  /**
   * Unhandled instruction.
   * @param ins ignored
   */
  @Override
  public void visitBREAKPOINT(final BREAKPOINT ins) {
    fRes = Util.unhandled(ins);
  }
  
  @Override
  public void visitConversionInstruction(final ConversionInstruction ins) {
    switch (ins.getOpcode()) {
      case Constants.I2B:
      case Constants.I2S:
        fRes = Util.upCase(ins.getName());
      default:
        fRes = Util.unhandled(ins);
    }
  }
  
  @Override
  public void visitCPInstruction(final CPInstruction ins) {
    final String name = Util.upCase(ins.getName());
    final Repository fRepos = SyntheticRepository.getInstance();
    final Type type = ((CPInstruction) ins).getType(fConstantPool);
    if (ins instanceof ANEWARRAY) {
      try {
        fRes = "Newarray " + Util.convertType(type, fRepos);
      } 
      catch (ClassNotFoundException e) {
        e.printStackTrace();
      }
    } 
    else if (ins instanceof CHECKCAST) {
      try {
        fRes = name + " " + Util.convertReferenceType((ReferenceType) type, fRepos);
      }
      catch (ClassNotFoundException e) {
        e.printStackTrace();
      }
    } 
    else if (ins instanceof FieldOrMethod) {
      final FieldOrMethod fom = (FieldOrMethod) ins;
      final String className = Util.coqify(fom.getReferenceType(fConstantPool).toString());
      // String fmName = coqify(fom.getName(cpg));
      if (ins instanceof FieldInstruction) {
        final String fs = className + "Signature." + 
            Util.coqify(fom.getName(fConstantPool)) + "FieldSignature";
        fRes = name + " " + fs;
      } 
      else if (ins instanceof InvokeInstruction) {
        String ms;
        ms = className + "Signature" + "." + 
             fMethodHandler.getName((InvokeInstruction) fom, fConstantPool) + 
             "Signature";

        fRes = name + " " + ms;
      } 
      else {
        fRes = Util.unknown("FieldOrMethod", ins);
      }
    } 
    else if (ins instanceof INSTANCEOF) {
      try {
        fRes = name + " " + Util.convertReferenceType((ReferenceType) type, fRepos);
      }
      catch (ClassNotFoundException e) {
        e.printStackTrace();
      }
    } 
    else if (ins instanceof LDC) {
      fRes = Util.unhandled(ins);
    } 
    else if (ins instanceof LDC2_W) {
      fRes = Util.unhandled(ins);
    } 
    else if (ins instanceof MULTIANEWARRAY) {
      fRes = Util.unhandled(ins);
    } 
    else if (ins instanceof NEW) {
      fRes = name + " " + 
           Util.coqify(((NEW) ins).getType(fConstantPool).toString()) + 
             ".className";
      // convertType(type);
    } 
    else {
      fRes = Util.unknown("CPInstruction", ins);
    }
  }
  
  /**
   * Unhandled instruction.
   * @param ins ignored
   */
  @Override
  public void visitDCMPG(final DCMPG ins) {
    fRes = Util.unhandled(ins);
  }
  
  /**
   * Unhandled instruction.
   * @param ins ignored
   */
  @Override
  public void visitDCMPL(final DCMPL ins) {
    fRes = Util.unhandled(ins);
  }
  
  /**
   * Unhandled instruction.
   * @param ins ignored
   */
  @Override
  public void visitDCONST(final DCONST ins) {
    fRes = Util.unhandled(ins);
  }
  
  /**
   * Unhandled instruction.
   * @param ins ignored
   */
  @Override
  public void visitFCMPG(final FCMPG ins) {
    fRes = Util.unhandled(ins);
  }
  
  /**
   * Unhandled instruction.
   * @param ins ignored
   */
  @Override
  public void visitFCMPL(final FCMPL ins) {
    fRes = Util.unhandled(ins);
  }
  
  /**
   * Unhandled instruction.
   * @param ins ignored
   */
  @Override
  public void visitFCONST(final FCONST ins) {
    fRes = Util.unhandled(ins);
  }
  
  /**
   * Unhandled instruction.
   * @param ins ignored
   */
  @Override
  public void visitICONST(final ICONST ins) {
    fRes = "Const INT " + Util.printZ(((ICONST) ins).getValue());
  }
  
  /**
   * Unhandled instruction.
   * @param ins ignored
   */
  @Override
  public void visitIMPDEP1(final IMPDEP1 ins) {
    fRes = Util.unhandled(ins);
  }
  
  /**
   * Unhandled instruction.
   * @param ins ignored
   */
  @Override
  public void visitIMPDEP2(final IMPDEP2 ins) {
    fRes = Util.unhandled(ins);
  }
  
  /**
   * Unhandled instruction.
   * @param ins ignored
   */
  @Override
  public void visitLCMP(final LCMP ins) {
    fRes = Util.unhandled(ins);
  }
  
  /**
   * Unhandled instruction.
   * @param ins ignored
   */
  @Override
  public void visitLCONST(final LCONST ins) {
    fRes = Util.unhandled(ins);
  }
  
  @Override
  public void visitLocalVariableInstruction(final LocalVariableInstruction ins) {
    final int index = ((LocalVariableInstruction) ins).getIndex();
    String name = Util.upCase(ins.getName());
    if (ins instanceof IINC) {
      fRes = name + " " + index + "%N " + Util.printZ(((IINC) ins).getIncrement());
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
        fRes = "V" + name.substring(1) + " " + c + "val " + index + "%N";
      } 
      else if (c == 'D' || c == 'F' || c == 'L') {
        fRes = Util.unhandled("LocalVariableInstruction", ins);
      } 
      else {
        fRes = Util.unknown("LocalVariableInstruction", ins);
      }
    }
  }
  
  /**
   * Unhandled instruction.
   * @param ins ignored
   */
  @Override
  public void visitMONITORENTER(final MONITORENTER ins) {
    fRes = Util.unhandled(ins);
  }
  
  /**
   * Unhandled instruction.
   * @param ins ignored
   */
  @Override
  public void visitMONITOREXIT(final MONITOREXIT ins) {
    fRes = Util.unhandled(ins);
  }
  
  /**
   * Set the result to <code>Newarray type</code>.
   * @param ins parameter from where the type information is gotten
   */
  @Override
  public void visitNEWARRAY(final NEWARRAY ins) {
    try {
      final String type = Util.convertType(BasicType.getType(((NEWARRAY) ins)
                                                  .getTypecode()), null);
      fRes = "Newarray " + type;
    } 
    catch (ClassNotFoundException e) {
      e.printStackTrace();
    }
  }
  
  /**
   * Set the result to <code>Nop</code>.
   * @param ins ignored
   */
  @Override
  public void visitNOP(final NOP ins) {
    fRes = "Nop";
  }
  
  /**
   * Unhandled instruction.
   * @param ins ignored
   */
  @Override
  public void visitRET(final RET ins) {
    fRes = Util.unhandled(ins);
  }
  
  @Override
  public void visitReturnInstruction(final ReturnInstruction ins) {
    final String name = Util.upCase(ins.getName());
    final char c = name.charAt(0);
    if (c == 'R') { // return nothing
      fRes = name;
    } 
    else if (c == 'A' || c == 'I') {
      // Areturn -> Vreturn Aval
      // Ireturn -> Vreturn Ival
      fRes = "Vreturn " + c + "val";
    } 
    else if (c == 'D' || c == 'F' || c == 'L') {
      fRes = Util.unhandled("ReturnInstruction", ins);
    } 
    else {
      fRes = Util.unknown("ReturnInstruction", ins);
    }
  }
  
  /**
   * Set the result to <code>Const SHORT num</code>.
   * @param ins parameter from where the number is taken
   */
  @Override
  public void visitSIPUSH(final SIPUSH ins) {
    fRes = "Const SHORT " + Util.printZ(((SIPUSH) ins).getValue());
  }
  
  @Override
  public void visitStackInstruction(final StackInstruction ins) {
    fRes = Util.upCase(ins.getName());
  }
  
  /**
   * Translate the given instruction to a Bicolano version of it.
   * @param metHandler the coq method names
   * @param constPool the constant pool associated with
   * these instructions
   * @param ins the instruction to translate
   * @return the bicolano compatible translation
   */
  public static String translate(final MethodHandler metHandler, 
                                 final ConstantPoolGen constPool, 
                                 final Instruction ins) {
    final InstructionVisitor v = new InstructionVisitor(metHandler, constPool);
    ins.accept(v);
    if (v.fRes.equals("")) {
      v.fRes = Util.unknown("Instruction", ins);
    }
    
    return v.fRes;
  }

}
