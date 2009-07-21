/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import org.apache.bcel.generic.BranchInstruction;
import org.apache.bcel.generic.GOTO;
import org.apache.bcel.generic.GOTO_W;
import org.apache.bcel.generic.IFEQ;
import org.apache.bcel.generic.IFGE;
import org.apache.bcel.generic.IFGT;
import org.apache.bcel.generic.IFLE;
import org.apache.bcel.generic.IFLT;
import org.apache.bcel.generic.IFNE;
import org.apache.bcel.generic.IFNONNULL;
import org.apache.bcel.generic.IFNULL;
import org.apache.bcel.generic.IF_ACMPEQ;
import org.apache.bcel.generic.IF_ACMPNE;
import org.apache.bcel.generic.IF_ICMPEQ;
import org.apache.bcel.generic.IF_ICMPGE;
import org.apache.bcel.generic.IF_ICMPGT;
import org.apache.bcel.generic.IF_ICMPLE;
import org.apache.bcel.generic.IF_ICMPLT;
import org.apache.bcel.generic.IF_ICMPNE;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.JSR;
import org.apache.bcel.generic.JSR_W;

import umbra.UmbraHelper;
import umbra.UmbraPlugin;
import umbra.editor.parsing.BytecodeStrings;


/**
 * This class is related to some subset of instructions
 * depending on parameters. It redefines some crucial while
 * handling with single instruction methods(correctness, getting handle).
 * Instructions of this class are responsible for jumping in code.
 * Their specificity is having target.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class JumpInstruction extends NumInstruction {


  /**
   * TODO not generalized !-3, this magic number must be replaced with a
   * better heuristic to deal with the case when the target jump line does
   * not exist.
   */
  private static final int MAGIC_THREE = 3;

  /**
   * This creates an instance of an instruction
   * named as <code>a_name</code> in a line the text of which is
   * <code>a_line</code>. Currently it just calls the constructor of the
   * superclass.
   *
   * @param a_line_text the line number of the instruction
   * @param a_name the mnemonic name of the instruction
   * @see InstructionLineController#InstructionLineController(String, String)
   */
  public JumpInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }



  /**
   * Jump instruction line is correct if it has
   * one number parameter preceded by #.
   *
   * @return <code>true</code> when the current line of the bytecode is
   *         correctly formatted jump instruction
   * @see InstructionLineController#correct()
   */
  public final boolean correct() {
    final String s = UmbraHelper.stripAllWhitespace(getMy_line_text());
    final String[] s2 = BytecodeStrings.JUMP_INS;
    if (s.indexOf("#") < s.indexOf(":") + 1) return false;
    // we check all the instructions in s2
    int res = 0;
    for (int j = 0; j < s2.length; j++) {
      res = checkInstructionWithNumber(s, s2[j], '#');
      if (res != 0) return res > 0;
    }
    return false;
  }

  /**
   * TODO.
   * @return TODO
   */
  private int getInd() {
    final String my_line_text = getMy_line_text();
    boolean isd;
    final String counter = "0123456789";
    int number;

    isd = true;
    int upto = my_line_text.length(); //we seek the first non-digit character
                                      //after #
    for (int i = my_line_text.lastIndexOf("#") + 1;
         i < my_line_text.length(); i++) {
      if (!Character.isDigit(my_line_text.charAt(i))) {
        upto = i;
        break;
      }
    }
    if (isd) { //TODO is is necessary?
      number = 0;
      for (int i = my_line_text.lastIndexOf("#") + 1; i < upto; i++) {
        number = 10 * number +
                              counter.indexOf(my_line_text.substring(i, i + 1));
      }
      return number;
    }
    return 0;
  }

  /**
   * TODO.
   * @return TODO
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {
    final InstructionHandle ih = null;

    if (!correct())
      return null;
    Instruction res = null;
    if (getName().compareTo("goto") == 0) {
      res = new GOTO(ih);
    }
    if (getName().compareTo("goto_w") == 0) {
      res = new GOTO_W(ih);
    }
    if (getName().compareTo("if_acmpeq") == 0) {
      res = new IF_ACMPEQ(ih);
    }
    if (getName().compareTo("if_acmpne") == 0) {
      res = new IF_ACMPNE(ih);
    }
    if (getName().compareTo("if_icmpeq") == 0) {
      res = new IF_ICMPEQ(ih);
    }
    if (getName().compareTo("if_icmpge") == 0) {
      res = new IF_ICMPGE(ih);
    }
    if (getName().compareTo("if_icmpgt") == 0) {
      res = new IF_ICMPGT(ih);
    }
    if (getName().compareTo("if_icmple") == 0) {
      res = new IF_ICMPLE(ih);
    }
    if (getName().compareTo("if_icmplt") == 0) {
      res = new IF_ICMPLT(ih);
    }
    if (getName().compareTo("if_icmpne") == 0) {
      res = new IF_ICMPNE(ih);
    }
    if (getName().compareTo("ifeq") == 0) {
      res = new IFEQ(ih);
    }
    if (getName().compareTo("ifge") == 0) {
      res = new IFGE(ih);
    }
    if (getName().compareTo("ifgt") == 0) {
      res = new IFGT(ih);
    }
    if (getName().compareTo("ifle") == 0) {
      res = new IFLE(ih);
    }
    if (getName().compareTo("iflt") == 0) {
      res = new IFLT(ih);
    }
    if (getName().compareTo("ifne") == 0) {
      res = new IFNE(ih);
    }
    if (getName().compareTo("ifnonnull") == 0) {
      res = new IFNONNULL(ih);
    }
    if (getName().compareTo("ifnull") == 0) {
      res = new IFNULL(ih);
    }
    if (getName().compareTo("jsr") == 0) {
      res = new JSR(ih);
    }
    if (getName().compareTo("jsr_w") == 0) {
      res = new JSR_W(ih);
    }
    return res;
  }

  /**
   * Jump instruction requires an instruction number of
   * its target as a parameter. This method is resposible
   * for setting such a number. The case that target line
   * does not exist is not completely solved yet.
   *
   * @param an_ins_list an instruction list with the jump instruction
   * @param an_ins the jump instruction to set the target for
   * @see umbra.instructions.BytecodeLineController#setTarget(
   *                            org.apache.bcel.generic.InstructionList,
   *                            org.apache.bcel.generic.Instruction)
   */
  public final void setTarget(final InstructionList an_ins_list,
                              final Instruction an_ins) {
    int i = 0;
    i = getInd();
    InstructionHandle iha = null;
    // add parameter to getInstruction
    iha = an_ins_list.findHandle(i);
    if (iha == null) iha = an_ins_list.findHandle(i - MAGIC_THREE);
    UmbraPlugin.messagelog("i = " + i);
    if (an_ins_list == null) UmbraPlugin.messagelog("null il");
    else if (iha == null) UmbraPlugin.messagelog("null iha");
    else if (iha.getInstruction() == null)
        UmbraPlugin.messagelog("null ins (drugie)");
    else UmbraPlugin.messagelog(iha.getInstruction().getName());
    if (an_ins == null) UmbraPlugin.messagelog("null ins");
    else UmbraPlugin.messagelog(an_ins.getName());
    ((BranchInstruction)an_ins).setTarget(iha);
    //UmbraPlugin.messagelog("Just failed");
  }
}
