/*
 * Created on 2005-05-19
 *
 */
package umbra.instructions;

import org.apache.bcel.generic.*;

import umbra.UmbraHelper;
import umbra.editor.parsing.IBytecodeStrings;


/**
 * This class is related to some subset of instructions
 * depending on parameters. It redefines some crucial while
 * handling with single instruction methods(correctness, getting handle).
 * Various instructions with no parameter.
 *
 * @author Jaros�aw Paszek
 */
public class SingleInstruction extends InstructionLineController {

  /**
   * TODO
   */
  public SingleInstruction(final String l, final String n) {
    super(l, n);
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
    if (name.compareTo("aconst_null")==0) return new ACONST_NULL();
    if (name.compareTo("dadd")==0) return new DADD();
    if (name.compareTo("ddiv")==0) return new DDIV();
    if (name.compareTo("dmul")==0) return new DMUL();
    if (name.compareTo("dneg")==0) return new DNEG();
    if (name.compareTo("drem")==0) return new DREM();
    if (name.compareTo("dsub")==0) return new DSUB();
    if (name.compareTo("fadd")==0) return new FADD();
    if (name.compareTo("fdiv")==0) return new FDIV();
    if (name.compareTo("fmul")==0) return new FMUL();
    if (name.compareTo("fneg")==0) return new FNEG();
    if (name.compareTo("frem")==0) return new FREM();
    if (name.compareTo("fsub")==0) return new FSUB();
    if (name.compareTo("iadd")==0) return new IADD();
    if (name.compareTo("iand")==0) return new IAND();
    if (name.compareTo("imul")==0) return new IMUL();
    if (name.compareTo("idiv")==0) return new IDIV();
    if (name.compareTo("ineg")==0) return new INEG();
    if (name.compareTo("ior")==0) return new IOR();
    if (name.compareTo("isub")==0) return new ISUB();
    if (name.compareTo("irem")==0) return new IREM();
    if (name.compareTo("iushr")==0) return new IUSHR();
    if (name.compareTo("ixor")==0) return new IXOR();
    if (name.compareTo("lsub")==0) return new LSUB();
    if (name.compareTo("ladd")==0) return new LADD();
    if (name.compareTo("land")==0) return new LAND();
    if (name.compareTo("ldiv")==0) return new LDIV();
    if (name.compareTo("lmul")==0) return new LMUL();
    if (name.compareTo("lneg")==0) return new LNEG();
    if (name.compareTo("lor")==0) return new LOR();
    if (name.compareTo("lrem")==0) return new LREM();
    if (name.compareTo("lshl")==0) return new LSHL();
    if (name.compareTo("lshr")==0) return new LSHR();
    if (name.compareTo("lushr")==0) return new LUSHR();
    if (name.compareTo("lxor")==0) return new LXOR();
    if (name.compareTo("aaload")==0) return new AALOAD();
    if (name.compareTo("aastore")==0) return new AASTORE();
    if (name.compareTo("baload")==0) return new BALOAD();
    if (name.compareTo("bastore")==0) return new BASTORE();
    if (name.compareTo("caload")==0) return new CALOAD();
    if (name.compareTo("castore")==0) return new CASTORE();
    if (name.compareTo("daload")==0) return new DALOAD();
    if (name.compareTo("dastore")==0) return new DASTORE();
    if (name.compareTo("faload")==0) return new FALOAD();
    if (name.compareTo("fastore")==0) return new FASTORE();
    if (name.compareTo("iaload")==0) return new IALOAD();
    if (name.compareTo("iastore")==0) return new IASTORE();
    if (name.compareTo("laload")==0) return new LALOAD();
    if (name.compareTo("lastore")==0) return new LASTORE();
    if (name.compareTo("saload")==0) return new SALOAD();
    if (name.compareTo("sastore")==0) return new SASTORE();
    if (name.compareTo("arraylength")==0) return new ARRAYLENGTH();
    if (name.compareTo("athrow")==0) return new ATHROW();
    if (name.compareTo("iconst_0")==0) return new ICONST(0);
    if (name.compareTo("iconst_1")==0) return new ICONST(1);
    if (name.compareTo("iconst_2")==0) return new ICONST(2);
    if (name.compareTo("iconst_3")==0) return new ICONST(3);
    if (name.compareTo("iconst_4")==0) return new ICONST(4);
    if (name.compareTo("iconst_5")==0) return new ICONST(5);
    if (name.compareTo("iconst_m1")==0) return new ICONST(-1);
    if (name.compareTo("lcmp")==0) return new LCMP();
    if (name.compareTo("aload_0")==0) return new ALOAD(0);
    if (name.compareTo("aload_1")==0) return new ALOAD(1);
    if (name.compareTo("aload_2")==0) return new ALOAD(2);
    if (name.compareTo("aload_3")==0) return new ALOAD(3);
    if (name.compareTo("astore_0")==0) return new ASTORE(0);
    if (name.compareTo("astore_1")==0) return new ASTORE(1);
    if (name.compareTo("astore_2")==0) return new ASTORE(2);
    if (name.compareTo("astore_3")==0) return new ASTORE(3);
    if (name.compareTo("dload_0")==0) return new DLOAD(0);
    if (name.compareTo("dload_1")==0) return new DLOAD(1);
    if (name.compareTo("dload_2")==0) return new DLOAD(2);
    if (name.compareTo("dload_3")==0) return new DLOAD(3);
    if (name.compareTo("dstore_0")==0) return new DSTORE(0);
    if (name.compareTo("dstore_1")==0) return new DSTORE(1);
    if (name.compareTo("dstore_2")==0) return new DSTORE(2);
    if (name.compareTo("dstore_3")==0) return new DSTORE(3);
    if (name.compareTo("fload_0")==0) return new FLOAD(0);
    if (name.compareTo("fload_1")==0) return new FLOAD(1);
    if (name.compareTo("fload_2")==0) return new FLOAD(2);
    if (name.compareTo("fload_3")==0) return new FLOAD(3);
    if (name.compareTo("fstore_0")==0) return new FSTORE(0);
    if (name.compareTo("fstore_1")==0) return new FSTORE(1);
    if (name.compareTo("fstore_2")==0) return new FSTORE(2);
    if (name.compareTo("fstore_3")==0) return new FSTORE(3);
    if (name.compareTo("iload_0")==0) return new ILOAD(0);
    if (name.compareTo("iload_1")==0) return new ILOAD(1);
    if (name.compareTo("iload_2")==0) return new ILOAD(2);
    if (name.compareTo("iload_3")==0) return new ILOAD(3);
    if (name.compareTo("istore_0")==0) return new ISTORE(0);
    if (name.compareTo("istore_1")==0) return new ISTORE(1);
    if (name.compareTo("istore_2")==0) return new ISTORE(2);
    if (name.compareTo("istore_3")==0) return new ISTORE(3);
    if (name.compareTo("lload_0")==0) return new LLOAD(0);
    if (name.compareTo("lload_1")==0) return new LLOAD(1);
    if (name.compareTo("lload_2")==0) return new LLOAD(2);
    if (name.compareTo("lload_3")==0) return new LLOAD(3);
    if (name.compareTo("lstore_0")==0) return new LSTORE(0);
    if (name.compareTo("lstore_1")==0) return new LSTORE(1);
    if (name.compareTo("lstore_2")==0) return new LSTORE(2);
    if (name.compareTo("lstore_3")==0) return new LSTORE(3);
    if (name.compareTo("monitorenter")==0) return new MONITORENTER();
    if (name.compareTo("monitorexit")==0) return new MONITOREXIT();
    if (name.compareTo("areturn")==0) return new ARETURN();
    if (name.compareTo("dreturn")==0) return new DRETURN();
    if (name.compareTo("freturn")==0) return new FRETURN();
    if (name.compareTo("ireturn")==0) return new IRETURN();
    if (name.compareTo("lreturn")==0) return new LRETURN();
    if (name.compareTo("return")==0) return new RETURN();
    if (name.compareTo("dup")==0) return new DUP();
    if (name.compareTo("dup_x1")==0) return new DUP_X1();
    if (name.compareTo("dup_x2")==0) return new DUP_X2();
    if (name.compareTo("dup2")==0) return new DUP2();
    if (name.compareTo("dup2_x1")==0) return new DUP2_X1();
    if (name.compareTo("dup2_x2")==0) return new DUP2_X2();
    if (name.compareTo("pop")==0) return new POP();
    if (name.compareTo("pop2")==0) return new POP2();
    if (name.compareTo("swap")==0) return new SWAP();
    return null;
  }

  /**
   * Simple instruction line is correct if it has
   * no parameter
   *
   *@see InstructionLineController#correct()
   */
  public final boolean correct()
  {
    String s;
    s = UmbraHelper.stripAllWhitespace(line);
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
