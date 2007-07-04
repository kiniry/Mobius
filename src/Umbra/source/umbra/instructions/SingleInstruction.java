/*
 * Created on 2005-05-19
 *
 */
package umbra.instructions;

import org.apache.bcel.generic.AALOAD;
import org.apache.bcel.generic.AASTORE;
import org.apache.bcel.generic.ACONST_NULL;
import org.apache.bcel.generic.ALOAD;
import org.apache.bcel.generic.ARETURN;
import org.apache.bcel.generic.ARRAYLENGTH;
import org.apache.bcel.generic.ASTORE;
import org.apache.bcel.generic.ATHROW;
import org.apache.bcel.generic.BALOAD;
import org.apache.bcel.generic.BASTORE;
import org.apache.bcel.generic.CALOAD;
import org.apache.bcel.generic.CASTORE;
import org.apache.bcel.generic.DADD;
import org.apache.bcel.generic.DALOAD;
import org.apache.bcel.generic.DASTORE;
import org.apache.bcel.generic.DDIV;
import org.apache.bcel.generic.DLOAD;
import org.apache.bcel.generic.DMUL;
import org.apache.bcel.generic.DNEG;
import org.apache.bcel.generic.DREM;
import org.apache.bcel.generic.DRETURN;
import org.apache.bcel.generic.DSTORE;
import org.apache.bcel.generic.DSUB;
import org.apache.bcel.generic.DUP;
import org.apache.bcel.generic.DUP2;
import org.apache.bcel.generic.DUP2_X1;
import org.apache.bcel.generic.DUP2_X2;
import org.apache.bcel.generic.DUP_X1;
import org.apache.bcel.generic.DUP_X2;
import org.apache.bcel.generic.FADD;
import org.apache.bcel.generic.FALOAD;
import org.apache.bcel.generic.FASTORE;
import org.apache.bcel.generic.FDIV;
import org.apache.bcel.generic.FLOAD;
import org.apache.bcel.generic.FMUL;
import org.apache.bcel.generic.FNEG;
import org.apache.bcel.generic.FREM;
import org.apache.bcel.generic.FRETURN;
import org.apache.bcel.generic.FSTORE;
import org.apache.bcel.generic.FSUB;
import org.apache.bcel.generic.IADD;
import org.apache.bcel.generic.IALOAD;
import org.apache.bcel.generic.IAND;
import org.apache.bcel.generic.IASTORE;
import org.apache.bcel.generic.ICONST;
import org.apache.bcel.generic.IDIV;
import org.apache.bcel.generic.ILOAD;
import org.apache.bcel.generic.IMUL;
import org.apache.bcel.generic.INEG;
import org.apache.bcel.generic.IOR;
import org.apache.bcel.generic.IREM;
import org.apache.bcel.generic.IRETURN;
import org.apache.bcel.generic.ISTORE;
import org.apache.bcel.generic.ISUB;
import org.apache.bcel.generic.IUSHR;
import org.apache.bcel.generic.IXOR;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.LADD;
import org.apache.bcel.generic.LALOAD;
import org.apache.bcel.generic.LAND;
import org.apache.bcel.generic.LASTORE;
import org.apache.bcel.generic.LCMP;
import org.apache.bcel.generic.LDIV;
import org.apache.bcel.generic.LLOAD;
import org.apache.bcel.generic.LMUL;
import org.apache.bcel.generic.LNEG;
import org.apache.bcel.generic.LOR;
import org.apache.bcel.generic.LREM;
import org.apache.bcel.generic.LRETURN;
import org.apache.bcel.generic.LSHL;
import org.apache.bcel.generic.LSHR;
import org.apache.bcel.generic.LSTORE;
import org.apache.bcel.generic.LSUB;
import org.apache.bcel.generic.LUSHR;
import org.apache.bcel.generic.LXOR;
import org.apache.bcel.generic.MONITORENTER;
import org.apache.bcel.generic.MONITOREXIT;
import org.apache.bcel.generic.POP;
import org.apache.bcel.generic.POP2;
import org.apache.bcel.generic.RETURN;
import org.apache.bcel.generic.SALOAD;
import org.apache.bcel.generic.SASTORE;
import org.apache.bcel.generic.SWAP;

import umbra.UmbraHelper;
import umbra.editor.parsing.IBytecodeStrings;


/**
 * This class is related to some subset of instructions
 * depending on parameters. It redefines some crucial while
 * handling with single instruction methods(correctness, getting handle).
 * Various instructions with no parameter.
 * TODO rewrite the description
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class SingleInstruction extends InstructionLineController {

  /**
   * The constant that with a built-in instruction numeric parameter 0.
   */
  private static final int BUILTIN_NUMBER_0 = 0;

  /**
   * The constant that with a built-in instruction numeric parameter 1.
   */
  private static final int BUILTIN_NUMBER_1 = 1;

  /**
   * The constant that with a built-in instruction numeric parameter 2.
   */
  private static final int BUILTIN_NUMBER_2 = 2;

  /**
   * The constant that with a built-in instruction numeric parameter 3.
   */
  private static final int BUILTIN_NUMBER_3 = 3;

  /**
   * The constant that with a built-in instruction numeric parameter 4.
   */
  private static final int BUILTIN_NUMBER_4 = 4;

  /**
   * The constant that with a built-in instruction numeric parameter 5.
   */
  private static final int BUILTIN_NUMBER_5 = 5;

  /**
   * This creates an instance of an instruction
   * named as <code>a_name</code> with the line text
   * <code>a_line</code>. Currently it just calls the constructor of the
   * superclass.
   *
   * @param a_line_text the line number of the instruction
   * @param a_name the mnemonic name of the instruction
   * @see InstructionLineController#InstructionLineController(String, String)
   */
  public SingleInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }

  /**
   * TODO
   *
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {
    //&*
    if (!correct())
      return null;
    if (name.compareTo("aconst_null") == 0) return new ACONST_NULL();
    if (name.compareTo("dadd") == 0) return new DADD();
    if (name.compareTo("ddiv") == 0) return new DDIV();
    if (name.compareTo("dmul") == 0) return new DMUL();
    if (name.compareTo("dneg") == 0) return new DNEG();
    if (name.compareTo("drem") == 0) return new DREM();
    if (name.compareTo("dsub") == 0) return new DSUB();
    if (name.compareTo("fadd") == 0) return new FADD();
    if (name.compareTo("fdiv") == 0) return new FDIV();
    if (name.compareTo("fmul") == 0) return new FMUL();
    if (name.compareTo("fneg") == 0) return new FNEG();
    if (name.compareTo("frem") == 0) return new FREM();
    if (name.compareTo("fsub") == 0) return new FSUB();
    if (name.compareTo("iadd") == 0) return new IADD();
    if (name.compareTo("iand") == 0) return new IAND();
    if (name.compareTo("imul") == 0) return new IMUL();
    if (name.compareTo("idiv") == 0) return new IDIV();
    if (name.compareTo("ineg") == 0) return new INEG();
    if (name.compareTo("ior") == 0) return new IOR();
    if (name.compareTo("isub") == 0) return new ISUB();
    if (name.compareTo("irem") == 0) return new IREM();
    if (name.compareTo("iushr") == 0) return new IUSHR();
    if (name.compareTo("ixor") == 0) return new IXOR();
    if (name.compareTo("lsub") == 0) return new LSUB();
    if (name.compareTo("ladd") == 0) return new LADD();
    if (name.compareTo("land") == 0) return new LAND();
    if (name.compareTo("ldiv") == 0) return new LDIV();
    if (name.compareTo("lmul") == 0) return new LMUL();
    if (name.compareTo("lneg") == 0) return new LNEG();
    if (name.compareTo("lor") == 0) return new LOR();
    if (name.compareTo("lrem") == 0) return new LREM();
    if (name.compareTo("lshl") == 0) return new LSHL();
    if (name.compareTo("lshr") == 0) return new LSHR();
    if (name.compareTo("lushr") == 0) return new LUSHR();
    if (name.compareTo("lxor") == 0) return new LXOR();
    if (name.compareTo("aaload") == 0) return new AALOAD();
    if (name.compareTo("aastore") == 0) return new AASTORE();
    if (name.compareTo("baload") == 0) return new BALOAD();
    if (name.compareTo("bastore") == 0) return new BASTORE();
    if (name.compareTo("caload") == 0) return new CALOAD();
    if (name.compareTo("castore") == 0) return new CASTORE();
    if (name.compareTo("daload") == 0) return new DALOAD();
    if (name.compareTo("dastore") == 0) return new DASTORE();
    if (name.compareTo("faload") == 0) return new FALOAD();
    if (name.compareTo("fastore") == 0) return new FASTORE();
    if (name.compareTo("iaload") == 0) return new IALOAD();
    if (name.compareTo("iastore") == 0) return new IASTORE();
    if (name.compareTo("laload") == 0) return new LALOAD();
    if (name.compareTo("lastore") == 0) return new LASTORE();
    if (name.compareTo("saload") == 0) return new SALOAD();
    if (name.compareTo("sastore") == 0) return new SASTORE();
    if (name.compareTo("arraylength") == 0) return new ARRAYLENGTH();
    if (name.compareTo("athrow") == 0) return new ATHROW();
    if (name.compareTo("iconst_0") == 0) return new ICONST(BUILTIN_NUMBER_0);
    if (name.compareTo("iconst_1") == 0) return new ICONST(BUILTIN_NUMBER_1);
    if (name.compareTo("iconst_2") == 0) return new ICONST(BUILTIN_NUMBER_2);
    if (name.compareTo("iconst_3") == 0) return new ICONST(BUILTIN_NUMBER_3);
    if (name.compareTo("iconst_4") == 0) return new ICONST(BUILTIN_NUMBER_4);
    if (name.compareTo("iconst_5") == 0) return new ICONST(BUILTIN_NUMBER_5);
    // TODO is it really up to 5?
    if (name.compareTo("iconst_m1") == 0) return new ICONST(-1);
    if (name.compareTo("lcmp") == 0) return new LCMP();
    if (name.compareTo("aload_0") == 0) return new ALOAD(BUILTIN_NUMBER_0);
    if (name.compareTo("aload_1") == 0) return new ALOAD(BUILTIN_NUMBER_1);
    if (name.compareTo("aload_2") == 0) return new ALOAD(BUILTIN_NUMBER_2);
    if (name.compareTo("aload_3") == 0) return new ALOAD(BUILTIN_NUMBER_3);
    if (name.compareTo("astore_0") == 0) return new ASTORE(BUILTIN_NUMBER_0);
    if (name.compareTo("astore_1") == 0) return new ASTORE(BUILTIN_NUMBER_1);
    if (name.compareTo("astore_2") == 0) return new ASTORE(BUILTIN_NUMBER_2);
    if (name.compareTo("astore_3") == 0) return new ASTORE(BUILTIN_NUMBER_3);
    if (name.compareTo("dload_0") == 0) return new DLOAD(BUILTIN_NUMBER_0);
    if (name.compareTo("dload_1") == 0) return new DLOAD(BUILTIN_NUMBER_1);
    if (name.compareTo("dload_2") == 0) return new DLOAD(BUILTIN_NUMBER_2);
    if (name.compareTo("dload_3") == 0) return new DLOAD(BUILTIN_NUMBER_3);
    if (name.compareTo("dstore_0") == 0) return new DSTORE(BUILTIN_NUMBER_0);
    if (name.compareTo("dstore_1") == 0) return new DSTORE(BUILTIN_NUMBER_1);
    if (name.compareTo("dstore_2") == 0) return new DSTORE(BUILTIN_NUMBER_2);
    if (name.compareTo("dstore_3") == 0) return new DSTORE(BUILTIN_NUMBER_3);
    if (name.compareTo("fload_0") == 0) return new FLOAD(BUILTIN_NUMBER_0);
    if (name.compareTo("fload_1") == 0) return new FLOAD(BUILTIN_NUMBER_1);
    if (name.compareTo("fload_2") == 0) return new FLOAD(BUILTIN_NUMBER_2);
    if (name.compareTo("fload_3") == 0) return new FLOAD(BUILTIN_NUMBER_3);
    if (name.compareTo("fstore_0") == 0) return new FSTORE(BUILTIN_NUMBER_0);
    if (name.compareTo("fstore_1") == 0) return new FSTORE(BUILTIN_NUMBER_1);
    if (name.compareTo("fstore_2") == 0) return new FSTORE(BUILTIN_NUMBER_2);
    if (name.compareTo("fstore_3") == 0) return new FSTORE(BUILTIN_NUMBER_3);
    if (name.compareTo("iload_0") == 0) return new ILOAD(BUILTIN_NUMBER_0);
    if (name.compareTo("iload_1") == 0) return new ILOAD(BUILTIN_NUMBER_1);
    if (name.compareTo("iload_2") == 0) return new ILOAD(BUILTIN_NUMBER_2);
    if (name.compareTo("iload_3") == 0) return new ILOAD(BUILTIN_NUMBER_3);
    if (name.compareTo("istore_0") == 0) return new ISTORE(BUILTIN_NUMBER_0);
    if (name.compareTo("istore_1") == 0) return new ISTORE(BUILTIN_NUMBER_1);
    if (name.compareTo("istore_2") == 0) return new ISTORE(BUILTIN_NUMBER_2);
    if (name.compareTo("istore_3") == 0) return new ISTORE(BUILTIN_NUMBER_3);
    if (name.compareTo("lload_0") == 0) return new LLOAD(BUILTIN_NUMBER_0);
    if (name.compareTo("lload_1") == 0) return new LLOAD(BUILTIN_NUMBER_1);
    if (name.compareTo("lload_2") == 0) return new LLOAD(BUILTIN_NUMBER_2);
    if (name.compareTo("lload_3") == 0) return new LLOAD(BUILTIN_NUMBER_3);
    if (name.compareTo("lstore_0") == 0) return new LSTORE(BUILTIN_NUMBER_0);
    if (name.compareTo("lstore_1") == 0) return new LSTORE(BUILTIN_NUMBER_1);
    if (name.compareTo("lstore_2") == 0) return new LSTORE(BUILTIN_NUMBER_2);
    if (name.compareTo("lstore_3") == 0) return new LSTORE(BUILTIN_NUMBER_3);
    if (name.compareTo("monitorenter") == 0) return new MONITORENTER();
    if (name.compareTo("monitorexit") == 0) return new MONITOREXIT();
    if (name.compareTo("areturn") == 0) return new ARETURN();
    if (name.compareTo("dreturn") == 0) return new DRETURN();
    if (name.compareTo("freturn") == 0) return new FRETURN();
    if (name.compareTo("ireturn") == 0) return new IRETURN();
    if (name.compareTo("lreturn") == 0) return new LRETURN();
    if (name.compareTo("return") == 0) return new RETURN();
    if (name.compareTo("dup") == 0) return new DUP();
    if (name.compareTo("dup_x1") == 0) return new DUP_X1();
    if (name.compareTo("dup_x2") == 0) return new DUP_X2();
    if (name.compareTo("dup2") == 0) return new DUP2();
    if (name.compareTo("dup2_x1") == 0) return new DUP2_X1();
    if (name.compareTo("dup2_x2") == 0) return new DUP2_X2();
    if (name.compareTo("pop") == 0) return new POP();
    if (name.compareTo("pop2") == 0) return new POP2();
    if (name.compareTo("swap") == 0) return new SWAP();
    return null;
  }

  /**
   * Simple instruction line is correct if it has no parameter.
   *
   * @return <code>true</code> when the instruction mnemonic is the only text
   *         in the line of the instruction text
   * @see InstructionLineController#correct()
   */
  public final boolean correct() {
    final String s = UmbraHelper.stripAllWhitespace(my_line_text);
    final String[] s2 = IBytecodeStrings.single;
    int j;
    for (j = 0; j < s2.length; j++) {
      if ((s.indexOf(s2[j]) > 0) && (s.indexOf(s2[j]) < s.indexOf(":") + 2))
        if (((s.indexOf(s2[j])) + (s2[j].length())) == s.length())
          return true;
    }
    return false;
  }
}
