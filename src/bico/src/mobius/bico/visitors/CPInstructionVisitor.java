package mobius.bico.visitors;

import mobius.bico.Util;
import mobius.bico.bicolano.coq.CType;
import mobius.bico.dico.MethodHandler;

import org.apache.bcel.generic.ANEWARRAY;
import org.apache.bcel.generic.CHECKCAST;
import org.apache.bcel.generic.CPInstruction;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.EmptyVisitor;
import org.apache.bcel.generic.FieldInstruction;
import org.apache.bcel.generic.FieldOrMethod;
import org.apache.bcel.generic.INSTANCEOF;
import org.apache.bcel.generic.InvokeInstruction;
import org.apache.bcel.generic.LDC;
import org.apache.bcel.generic.LDC2_W;
import org.apache.bcel.generic.MULTIANEWARRAY;
import org.apache.bcel.generic.NEW;
import org.apache.bcel.generic.ReferenceType;
import org.apache.bcel.generic.Type;
import org.apache.bcel.util.Repository;
import org.apache.bcel.util.SyntheticRepository;


/**
 * Translate the Constant Pool instructions to bicolano friendly versions.
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class CPInstructionVisitor extends EmptyVisitor {
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
  private CPInstructionVisitor(final MethodHandler methodHandler,
                             final ConstantPoolGen constantPool) {
    fConstantPool = constantPool;
    fMethodHandler = methodHandler;
    fRes = "";
  }
  
  /**
   * Set the result to <code>Newarray type</code>.
   * @param ins parameter from where the type is taken
   */
  @Override
  public void visitANEWARRAY(final ANEWARRAY ins) {
    final Type type = ins.getType(fConstantPool);
    final Repository fRepos = SyntheticRepository.getInstance();
    try {
      fRes = "Newarray " + CType.getInstance().convertType(type, fRepos);
    } 
    catch (ClassNotFoundException e) {
      e.printStackTrace();
    }
  }
  
  
  /**
   * Set the result to <code>Checkcast type</code>.
   * @param ins parameter from where the type is taken
   */
  @Override
  public void visitCHECKCAST(final CHECKCAST ins) {
    final Type type = ins.getType(fConstantPool);
    final Repository fRepos = SyntheticRepository.getInstance();
    try {
      fRes = "Checkcast " + CType.getInstance().convertReferenceType((ReferenceType) type, fRepos);
    }
    catch (ClassNotFoundException e) {
      e.printStackTrace();
    }
  }
  
  /**
   * Set the result to a method or field access.
   * @param ins parameter from where the name of the method
   * or field are taken
   */
  @Override
  public void visitFieldOrMethod(final FieldOrMethod ins) {
    final String name = Util.upCase(ins.getName());
    final String className = Util.coqify(ins.getReferenceType(fConstantPool).toString());
    // String fmName = coqify(fom.getName(cpg));
    if (ins instanceof FieldInstruction) {
      final String fs = className + "Signature." + 
          Util.coqify(ins.getName(fConstantPool)) + "FieldSignature";
      fRes = name + " " + fs;
    } 
    else if (ins instanceof InvokeInstruction) {
      String ms;
      ms = className + "Signature" + "." + 
           fMethodHandler.getName((InvokeInstruction) ins, fConstantPool);

      fRes = name + " " + ms;
    } 
    else {
      fRes = Util.unknown("FieldOrMethod", ins);
    }
  }
  
  /**
   * Set the result to <code>Instanceof type</code>.
   * @param ins parameter from where the type is taken
   */
  @Override
  public void visitINSTANCEOF(final INSTANCEOF ins) {
    final Type type = ins.getType(fConstantPool);
    final Repository fRepos = SyntheticRepository.getInstance();
    try {
      fRes = "Instanceof " + CType.getInstance().convertReferenceType((ReferenceType) type, fRepos);
    }
    catch (ClassNotFoundException e) {
      e.printStackTrace();
    }
  }
  
  /**
   * Unhandled instruction.
   * @param ins ignored
   */
  @Override
  public void visitLDC(final LDC ins) {
    fRes = Util.unhandled(ins);
  }
  
  /**
   * Unhandled instruction.
   * @param ins ignored
   */
  @Override
  public void visitLDC2_W(final LDC2_W ins) {
    fRes = Util.unhandled(ins);
  }
  
  /**
   * Unhandled instruction.
   * @param ins ignored
   */
  @Override
  public void visitMULTIANEWARRAY(final MULTIANEWARRAY ins) {
    fRes = Util.unhandled(ins);
  }
  
  /**
   * Set the result to <code>New type</code>.
   * @param ins parameter from where the type is taken
   */
  @Override
  public void visitNEW(final NEW ins) {
    fRes = "New " + 
          Util.coqify(((NEW) ins).getType(fConstantPool).toString()) + 
          "Type.name";
  }
  
  /**
   * Translate the given Constant Pool instruction to a Bicolano version of it.
   * @param metHandler the coq method names
   * @param constPool the constant pool associated with
   * these instructions
   * @param ins the instruction to translate
   * @return the bicolano compatible translation
   */
  public static String translate (final MethodHandler metHandler,
                                  final ConstantPoolGen constPool, 
                                  final CPInstruction ins) {
    final CPInstructionVisitor v = new CPInstructionVisitor(metHandler, constPool);
    ins.accept(v);
    if (v.fRes.equals("")) {
      v.fRes = Util.unknown("CPInstruction", ins);
    }
    return v.fRes;
  }
}
