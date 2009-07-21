/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
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
import umbra.editor.parsing.BytecodeStrings;


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
   * TODO.
   * @return TODO
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {
    if (!correct())
      return null;
    Instruction res = null;
    if (getName().compareTo("aconst_null") == 0)
      res = new ACONST_NULL();
    res = getDoubleInstruction();
    if (getName().compareTo("fadd") == 0)
      res = new FADD();
    if (getName().compareTo("fdiv") == 0)
      res = new FDIV();
    if (getName().compareTo("fmul") == 0)
      res = new FMUL();
    if (getName().compareTo("fneg") == 0)
      res = new FNEG();
    if (getName().compareTo("frem") == 0)
      res = new FREM();
    if (getName().compareTo("fsub") == 0)
      res = new FSUB();
    if (getName().compareTo("iadd") == 0)
      res = new IADD();
    if (getName().compareTo("iand") == 0)
      res = new IAND();
    if (getName().compareTo("imul") == 0)
      res = new IMUL();
    if (getName().compareTo("idiv") == 0)
      res = new IDIV();
    if (getName().compareTo("ineg") == 0)
      res = new INEG();
    if (getName().compareTo("ior") == 0)
      res = new IOR();
    if (getName().compareTo("isub") == 0)
      res = new ISUB();
    if (getName().compareTo("irem") == 0)
      res = new IREM();
    if (getName().compareTo("iushr") == 0)
      res = new IUSHR();
    if (getName().compareTo("ixor") == 0)
      res = new IXOR();
    if (getName().compareTo("lsub") == 0)
      res = new LSUB();
    if (getName().compareTo("ladd") == 0)
      res = new LADD();
    if (getName().compareTo("land") == 0)
      res = new LAND();
    if (getName().compareTo("ldiv") == 0)
      res = new LDIV();
    if (getName().compareTo("lmul") == 0)
      res = new LMUL();
    if (getName().compareTo("lneg") == 0)
      res = new LNEG();
    if (getName().compareTo("lor") == 0)
      res = new LOR();
    if (getName().compareTo("lrem") == 0)
      res = new LREM();
    if (getName().compareTo("lshl") == 0)
      res = new LSHL();
    if (getName().compareTo("lshr") == 0)
      res = new LSHR();
    if (getName().compareTo("lushr") == 0)
      res = new LUSHR();
    if (getName().compareTo("lxor") == 0)
      res = new LXOR();
    if (getName().compareTo("aaload") == 0)
      res = new AALOAD();
    if (getName().compareTo("aastore") == 0)
      res = new AASTORE();
    if (getName().compareTo("baload") == 0)
      res = new BALOAD();
    if (getName().compareTo("bastore") == 0)
      res = new BASTORE();
    if (getName().compareTo("caload") == 0)
      res = new CALOAD();
    if (getName().compareTo("castore") == 0)
      res = new CASTORE();
    if (getName().compareTo("daload") == 0)
      res = new DALOAD();
    if (getName().compareTo("dastore") == 0)
      res = new DASTORE();
    if (getName().compareTo("faload") == 0)
      res = new FALOAD();
    if (getName().compareTo("fastore") == 0)
      res = new FASTORE();
    if (getName().compareTo("iaload") == 0)
      res = new IALOAD();
    if (getName().compareTo("iastore") == 0)
      res = new IASTORE();
    if (getName().compareTo("laload") == 0)
      res = new LALOAD();
    if (getName().compareTo("lastore") == 0)
      res = new LASTORE();
    if (getName().compareTo("saload") == 0)
      res = new SALOAD();
    if (getName().compareTo("sastore") == 0)
      res = new SASTORE();
    if (getName().compareTo("arraylength") == 0)
      res = new ARRAYLENGTH();
    if (getName().compareTo("athrow") == 0)
      res = new ATHROW();
    res = getIconstInstruction();
    if (getName().compareTo("lcmp") == 0)
      res = new LCMP();
    if (getName().compareTo("aload_0") == 0)
      res = new ALOAD(BUILTIN_NUMBER_0);
    if (getName().compareTo("aload_1") == 0)
      res = new ALOAD(BUILTIN_NUMBER_1);
    if (getName().compareTo("aload_2") == 0)
      res = new ALOAD(BUILTIN_NUMBER_2);
    if (getName().compareTo("aload_3") == 0)
      res = new ALOAD(BUILTIN_NUMBER_3);
    if (getName().compareTo("astore_0") == 0)
      res = new ASTORE(BUILTIN_NUMBER_0);
    if (getName().compareTo("astore_1") == 0)
      res = new ASTORE(BUILTIN_NUMBER_1);
    if (getName().compareTo("astore_2") == 0)
      res = new ASTORE(BUILTIN_NUMBER_2);
    if (getName().compareTo("astore_3") == 0)
      res = new ASTORE(BUILTIN_NUMBER_3);
    if (getName().compareTo("fload_0") == 0)
      res = new FLOAD(BUILTIN_NUMBER_0);
    if (getName().compareTo("fload_1") == 0)
      res = new FLOAD(BUILTIN_NUMBER_1);
    if (getName().compareTo("fload_2") == 0)
      res = new FLOAD(BUILTIN_NUMBER_2);
    if (getName().compareTo("fload_3") == 0)
      res = new FLOAD(BUILTIN_NUMBER_3);
    if (getName().compareTo("fstore_0") == 0)
      res = new FSTORE(BUILTIN_NUMBER_0);
    if (getName().compareTo("fstore_1") == 0)
      res = new FSTORE(BUILTIN_NUMBER_1);
    if (getName().compareTo("fstore_2") == 0)
      res = new FSTORE(BUILTIN_NUMBER_2);
    if (getName().compareTo("fstore_3") == 0)
      res = new FSTORE(BUILTIN_NUMBER_3);
    if (getName().compareTo("iload_0") == 0)
      res = new ILOAD(BUILTIN_NUMBER_0);
    if (getName().compareTo("iload_1") == 0)
      res = new ILOAD(BUILTIN_NUMBER_1);
    if (getName().compareTo("iload_2") == 0)
      res = new ILOAD(BUILTIN_NUMBER_2);
    if (getName().compareTo("iload_3") == 0)
      res = new ILOAD(BUILTIN_NUMBER_3);
    if (getName().compareTo("istore_0") == 0)
      res = new ISTORE(BUILTIN_NUMBER_0);
    if (getName().compareTo("istore_1") == 0)
      res = new ISTORE(BUILTIN_NUMBER_1);
    if (getName().compareTo("istore_2") == 0)
      res = new ISTORE(BUILTIN_NUMBER_2);
    if (getName().compareTo("istore_3") == 0)
      res = new ISTORE(BUILTIN_NUMBER_3);
    if (getName().compareTo("lload_0") == 0)
      res = new LLOAD(BUILTIN_NUMBER_0);
    if (getName().compareTo("lload_1") == 0)
      res = new LLOAD(BUILTIN_NUMBER_1);
    if (getName().compareTo("lload_2") == 0)
      res = new LLOAD(BUILTIN_NUMBER_2);
    if (getName().compareTo("lload_3") == 0)
      res = new LLOAD(BUILTIN_NUMBER_3);
    if (getName().compareTo("lstore_0") == 0)
      res = new LSTORE(BUILTIN_NUMBER_0);
    if (getName().compareTo("lstore_1") == 0)
      res = new LSTORE(BUILTIN_NUMBER_1);
    if (getName().compareTo("lstore_2") == 0)
      res = new LSTORE(BUILTIN_NUMBER_2);
    if (getName().compareTo("lstore_3") == 0)
      res = new LSTORE(BUILTIN_NUMBER_3);
    if (getName().compareTo("monitorenter") == 0)
      res = new MONITORENTER();
    if (getName().compareTo("monitorexit") == 0)
      res = new MONITOREXIT();
    if (getName().compareTo("areturn") == 0)
      res = new ARETURN();
    if (getName().compareTo("dreturn") == 0)
      res = new DRETURN();
    if (getName().compareTo("freturn") == 0)
      res = new FRETURN();
    if (getName().compareTo("ireturn") == 0)
      res = new IRETURN();
    if (getName().compareTo("lreturn") == 0)
      res = new LRETURN();
    if (getName().compareTo("return") == 0)
      res = new RETURN();
    if (getName().compareTo("dup") == 0)
      res = new DUP();
    if (getName().compareTo("dup_x1") == 0)
      res = new DUP_X1();
    if (getName().compareTo("dup_x2") == 0)
      res = new DUP_X2();
    if (getName().compareTo("dup2") == 0)
      res = new DUP2();
    if (getName().compareTo("dup2_x1") == 0)
      res = new DUP2_X1();
    if (getName().compareTo("dup2_x2") == 0)
      res = new DUP2_X2();
    if (getName().compareTo("pop") == 0)
      res = new POP();
    if (getName().compareTo("pop2") == 0)
      res = new POP2();
    if (getName().compareTo("swap") == 0)
      res = new SWAP();
    return res;
  }

  /**
   * This method checks if the current single instruction is one of the
   * instructions that operate on the double type. If so it returns appropriate
   * BCEL object, otherwise <code>null</code> is returned
   *
   * @return the appropriate BCEL object that represents an instruction which
   *   operates on the double type or <code>null</code>
   *   if no BCEL object for double types is appropriate
   */
  private Instruction getDoubleInstruction() {
    Instruction res = null;
    if (getName().compareTo("dadd") == 0)
      res = new DADD();
    if (getName().compareTo("ddiv") == 0)
      res = new DDIV();
    if (getName().compareTo("dmul") == 0)
      res = new DMUL();
    if (getName().compareTo("dneg") == 0)
      res = new DNEG();
    if (getName().compareTo("drem") == 0)
      res = new DREM();
    if (getName().compareTo("dsub") == 0)
      res = new DSUB();
    if (getName().compareTo("dload_0") == 0)
      res = new DLOAD(BUILTIN_NUMBER_0);
    if (getName().compareTo("dload_1") == 0)
      res = new DLOAD(BUILTIN_NUMBER_1);
    if (getName().compareTo("dload_2") == 0)
      res = new DLOAD(BUILTIN_NUMBER_2);
    if (getName().compareTo("dload_3") == 0)
      res = new DLOAD(BUILTIN_NUMBER_3);
    if (getName().compareTo("dstore_0") == 0)
      res = new DSTORE(BUILTIN_NUMBER_0);
    if (getName().compareTo("dstore_1") == 0)
      res = new DSTORE(BUILTIN_NUMBER_1);
    if (getName().compareTo("dstore_2") == 0)
      res = new DSTORE(BUILTIN_NUMBER_2);
    if (getName().compareTo("dstore_3") == 0)
      res = new DSTORE(BUILTIN_NUMBER_3);
    return res;
  }

  /**
   * This method checks if the current single instruction is one of the ICONST
   * instructions and returns appropriate BCEL {@link ICONST} object.
   *
   * @return the appropriate {@link ICONST} object or <code>null</code>
   *   if no ICONST object is appropriate
   */
  private Instruction getIconstInstruction() {
    Instruction res = null;
    if (getName().compareTo("iconst_0") == 0)
      res = new ICONST(BUILTIN_NUMBER_0);
    if (getName().compareTo("iconst_1") == 0)
      res = new ICONST(BUILTIN_NUMBER_1);
    if (getName().compareTo("iconst_2") == 0)
      res = new ICONST(BUILTIN_NUMBER_2);
    if (getName().compareTo("iconst_3") == 0)
      res = new ICONST(BUILTIN_NUMBER_3);
    if (getName().compareTo("iconst_4") == 0)
      res = new ICONST(BUILTIN_NUMBER_4);
    if (getName().compareTo("iconst_5") == 0)
      res = new ICONST(BUILTIN_NUMBER_5);
    // TODO is it really up to 5?
    if (getName().compareTo("iconst_m1") == 0)
      res = new ICONST(-1);
    return res;
  }

  /**
   * Simple instruction line is correct if it has no parameter.
   *
   * @return <code>true</code> when the instruction mnemonic is the only text
   *         in the line of the instruction text
   * @see InstructionLineController#correct()
   */
  public final boolean correct() {
    final String s = UmbraHelper.stripAllWhitespace(getMy_line_text());
    final String[] s2 = BytecodeStrings.SINGLE_INS;
    int j;
    for (j = 0; j < s2.length; j++) {
      if ((s.indexOf(s2[j]) > 0) &&
          (s.indexOf(s2[j]) <= s.indexOf(":") + 1)) // TODO why not ==
                                                    // instead of <=?
        if (((s.indexOf(s2[j])) + (s2[j].length())) == s.length())
          return true;
    }
    return false;
  }
}
