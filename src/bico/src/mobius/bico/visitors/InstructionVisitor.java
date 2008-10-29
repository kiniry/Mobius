package mobius.bico.visitors;

import mobius.bico.Util;
import mobius.bico.bicolano.AType;
import mobius.bico.bicolano.coq.CType;
import mobius.bico.bicolano.coq.Translator;
import mobius.bico.dico.MethodHandler;

import org.apache.bcel.Constants;
import org.apache.bcel.generic.ACONST_NULL;
import org.apache.bcel.generic.ARRAYLENGTH;
import org.apache.bcel.generic.ATHROW;
import org.apache.bcel.generic.ArithmeticInstruction;
import org.apache.bcel.generic.ArrayInstruction;
import org.apache.bcel.generic.BIPUSH;
import org.apache.bcel.generic.BREAKPOINT;
import org.apache.bcel.generic.BasicType;
import org.apache.bcel.generic.BranchInstruction;
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
import org.apache.bcel.generic.ICONST;
import org.apache.bcel.generic.IINC;
import org.apache.bcel.generic.IMPDEP1;
import org.apache.bcel.generic.IMPDEP2;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.LCMP;
import org.apache.bcel.generic.LCONST;
import org.apache.bcel.generic.LocalVariableInstruction;
import org.apache.bcel.generic.MONITORENTER;
import org.apache.bcel.generic.MONITOREXIT;
import org.apache.bcel.generic.NEWARRAY;
import org.apache.bcel.generic.NOP;
import org.apache.bcel.generic.RET;
import org.apache.bcel.generic.ReturnInstruction;
import org.apache.bcel.generic.SIPUSH;
import org.apache.bcel.generic.StackInstruction;
import org.apache.bcel.util.Repository;


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

  private final Repository fRepos;
  
  
  /**
   * Construct a new visitor.
   * @param methodHandler the coq method names
   * @param constantPool the constant pool associated with
   * these instructions
   */
  private InstructionVisitor(final MethodHandler methodHandler,
                             final ConstantPoolGen constantPool,
                             final Repository repos) {
    fConstantPool = constantPool;
    fMethodHandler = methodHandler;
    fRes = "";
    fRepos = repos;
  }
  
  
  /**
   * Set the result to <code>Aconst_null</code>.
   * @param ins ignored
   */
  @Override
  public void visitACONST_NULL(final ACONST_NULL ins) {
    fRes = "Aconst_null";
  }
  
  /** {@inheritDoc} */
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
    fRes = ArrayInstructionVisitor.translate(ins);
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
    fRes = "Const BYTE " + Translator.toZ(((BIPUSH) ins).getValue());
  }
  
  /**
   * Visits a BranchInstruction using the {@link BranchInstructionVisitor}
   * and sets the result in consequence.
   * @param ins the instruction which is passed to the called
   * visitor
   */
  @Override
  public void visitBranchInstruction(final BranchInstruction ins) {
    fRes = BranchInstructionVisitor.translate(ins);
  }
  

  
  /**
   * Visit a conversion instruction only works for I2B and
   * I2S.
   * @param ins the conversion instruction
   */
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
  
  
  /**
   * Visits a CPInstruction using the {@link CPInstructionVisitor}
   * and sets the result in consequence.
   * @param ins the instruction which is passed to the called
   * visitor
   */
  @Override
  public void visitCPInstruction(final CPInstruction ins) {
    fRes = CPInstructionVisitor.translate(fMethodHandler, 
                                   fConstantPool, ins);
  }
  

  
  /**
   * Construnt an integer constant.
   * @param ins contains the number
   */
  @Override
  public void visitICONST(final ICONST ins) {
    fRes = "Const INT " + Translator.toZ(((ICONST) ins).getValue());
  }
  

  
  /**
   * Construct a local variable. 
   * It can built Aload, Vload Aval, or outputs an error message.
   * @param ins the instruction to translate.
   */
  @Override
  public void visitLocalVariableInstruction(final LocalVariableInstruction ins) {
    final int index = ((LocalVariableInstruction) ins).getIndex();
    String name = Util.upCase(ins.getName());
    if (ins instanceof IINC) {
      fRes = name + " " + index + "%N " + Translator.toZ(((IINC) ins).getIncrement());
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
   * Set the result to <code>Newarray type</code>.
   * @param ins parameter from where the type information is gotten
   */
  @Override
  public void visitNEWARRAY(final NEWARRAY ins) {
    try {
      final AType type = CType.getInstance().convertType(BasicType.getType(((NEWARRAY) ins)
                                                  .getTypecode()), fRepos);
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
   * Translate a return instruction to a Bico one:
   * Return, Vreturn Aval, Vreturn Ival, or an unhandled
   * error message. 
   * @param ins the instruction to translate
   */
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
    fRes = "Const SHORT " + Translator.toZ(((SIPUSH) ins).getValue());
  }
  
  /** {@inheritDoc} */
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
                                 final Instruction ins,
                                 final Repository repos) {
    final InstructionVisitor v = new InstructionVisitor(metHandler, constPool, repos);
    ins.accept(v);
    if (v.fRes.equals("")) {
      v.fRes = Util.unknown("Instruction", ins);
    }
    
    return v.fRes;
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
   * Unhandled instruction.
   * @param ins ignored
   */
  @Override
  public void visitRET(final RET ins) {
    fRes = Util.unhandled(ins);
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
  public void visitBREAKPOINT(final BREAKPOINT ins) {
    fRes = Util.unhandled(ins);
  }
}
