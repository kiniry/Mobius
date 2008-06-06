/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

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

import umbra.instructions.InstructionParser;
import umbra.lib.BytecodeStrings;
import umbra.lib.UmbraException;


/**
 * This class handles the creation and correctness for jump instructions. The
 * jump instructions are:
 * <ul>
 *    <li>unconditional goto instructions,</li>
 *    <li>if instructions that compare references,</li>
 *    <li>if instructions that compare integers,</li>
 *    <li>if instructions that compare with null,</li>
 *    <li>if instructions that compare with 0,</li>
 *    <li>subroutine instructions.</li>
 * </ul>
 * FIXME: "lookupswitch", "tableswitch" are handled in a special simplified way.
 *        https://mobius.ucd.ie/ticket/552
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class JumpInstruction extends NumInstruction {

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
   * This method returns the array of jump instructions mnemonics.
   *
   * @return the array of the handled mnemonics
   * @see InstructionLineController#getMnemonics()
   */
  public static /*@ non_null @*/ String[] getMnemonics() {
    return BytecodeStrings.JUMP_INS;
  }

  /**
   * Jump instruction line is correct if it has one simple number parameter
   * preceded by '#'. The precise definition of this kind of a line is as
   * follows:
   *    whitespase number : whitespace mnemonic whitespace # number
   *    whitespace lineend
   * FIXME: tableswitch and lookupswitch are handled in a special way
   *        https://mobius.ucd.ie/ticket/552
   *
   * @return <code>true</code> when the syntax of the instruction line is
   *         correct
   * @see InstructionLineController#correct()
   */
  public final boolean correct() {
    boolean res = true;
    final InstructionParser parser = getParser();
    res = parseTillMnemonic(); //parse up to mnemonic
    res = res && (parser.swallowMnemonic(BytecodeStrings.JUMP_INS) >= 0);
                           //mnemonic
    if (BytecodeStrings.JUMP_INS[parser.getMnemonic()].equals("tableswitch")) {
      return true;
    }
    if (BytecodeStrings.JUMP_INS[parser.getMnemonic()].equals("lookupwitch")) {
      return true;
    }
    res = res && parser.swallowWhitespace(); //whitespace before the number
    res = res && parser.swallowDelimiter('#'); // #
    res = res && parser.swallowNumber(); // number
    res = res && !parser.swallowWhitespace();
    return res;
  }

  /**
   * This method parses the parameter of the current instruction.
   *
   * This method retrieves the numerical value of the parameter of the
   * instruction in {@link BytecodeLineController#getMy_line_text()}. This
   * parameter is located after the mnemonic followed by #. (with no
   * whitespace inbetween). The method assumes
   * {@link BytecodeLineController#getMy_line_text()} is correct.
   *
   * @return the value of the numerical parameter of the instruction

   */
  protected int getInd() {
    final InstructionParser parser = getParser();
    parser.resetParser();
    parser.seekMnemonic(BytecodeStrings.JUMP_INS); // mnemonic
    parser.swallowWhitespace(); //whitespace before the num
    parser.swallowDelimiter('#'); // #
    parser.swallowNumber(); // number
    return parser.getResult();
  }

  /**
   * This method, based on the value of the the mnemonic
   * name, creates a new BCEL instruction
   * object for a jump instruction, i.e.:
   * <ul>
   *    <li>unconditional goto instructions,</li>
   *    <li>if instructions that compare references,</li>
   *    <li>if instructions that compare integers,</li>
   *    <li>if instructions that compare with null,</li>
   *    <li>if instructions that compare with 0,</li>
   *    <li>subroutine instructions.</li>
   * </ul>
   *
   * This method also checks the syntactical correctness of the current
   * instruction line.
   *
   * @return the freshly constructed BCEL instruction or <code>null</code>
   *         in case the instruction is not a instruction from the current set
   *         and in case the instruction line is incorrect
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {
    final InstructionHandle ih = null;

    if (!correct())
      return null;
    Instruction res = null;
    res = getGotoInstruction(ih, res);
    res = getRefCompIfInstruction(ih, res);
    res = getIntCompIfInstruction(ih, res);
    res = getZeroCompIfInstruction(ih, res);
    res = getNullCompIfInstruction(ih, res);
    res = getSubroutineInstruction(ih, res);
    return res;
  }


  /**
   * This method creates the objects that represents a subroutine instruction.
   * It checks if the name of the current instruction is one of these and in
   * that case creates an appropriate object. In case the name is of a different
   * kind it returns the parameter <code>a_res</code>.
   *
   * The array instructions are:
   * <ul>
   *    <li>jsr,</li>
   *    <li>jsr_1.</li>
   * </ul>
   *
   * @param an_ih an instruction handle of the target instruction
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or a_res in
   *   case the current instruction is not in the current set
   */
  private Instruction getSubroutineInstruction(final InstructionHandle an_ih,
                                               final Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("jsr") == 0) {
      ires = new JSR(an_ih);
    }
    if (getName().compareTo("jsr_w") == 0) {
      ires = new JSR_W(an_ih);
    }
    return ires;
  }

  /**
   * This method creates the objects that represent if instructions that
   * compare with null references. It checks if the name of the current
   * instruction is one of these and in that case creates an appropriate object.
   * In case the name is of a different kind it returns the parameter
   * <code>a_res</code>.
   *
   * The array instructions are:
   * <ul>
   *    <li>ifnonnull,</li>
   *    <li>ifnull.</li>
   * </ul>
   *
   * @param an_ih an instruction handle of the target instruction
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or a_res in
   *   case the current instruction is not in the current set
   */
  private Instruction getNullCompIfInstruction(final InstructionHandle an_ih,
                                               final Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("ifnonnull") == 0) {
      ires = new IFNONNULL(an_ih);
    }
    if (getName().compareTo("ifnull") == 0) {
      ires = new IFNULL(an_ih);
    }
    return ires;
  }

  /**
   * This method creates the objects that represent if instructions that compare
   * with references. It checks if the name of the current instruction is one of
   * these and in that case creates an appropriate object. In case the name is
   * of a different kind it returns the parameter <code>a_res</code>.
   *
   * The array instructions are:
   * <ul>
   *    <li>if_acmpeq,</li>
   *    <li>if_acmpne.</li>
   * </ul>
   *
   * @param an_ih an instruction handle of the target instruction
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private Instruction getRefCompIfInstruction(final InstructionHandle an_ih,
                                              final Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("if_acmpeq") == 0) {
      ires = new IF_ACMPEQ(an_ih);
    }
    if (getName().compareTo("if_acmpne") == 0) {
      ires = new IF_ACMPNE(an_ih);
    }
    return ires;
  }

  /**
   * This method creates the objects that represent goto instructions.
   * It checks if the name of the current instruction is one of these and in
   * that case creates an appropriate object. In case the name is of a different
   * kind it returns the parameter <code>a_res</code>.
   *
   * The array instructions are:
   * <ul>
   *    <li>goto,</li>
   *    <li>goto_w.</li>
   * </ul>
   *
   * @param an_ih an instruction handle of the target instruction
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private Instruction getGotoInstruction(final InstructionHandle an_ih,
                                         final Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("goto") == 0) {
      ires = new GOTO(an_ih);
    }
    if (getName().compareTo("goto_w") == 0) {
      ires = new GOTO_W(an_ih);
    }
    return ires;
  }

  /**
   * This method creates the objects that represent if instructions to compare
   * with integers. It checks if the name of the current instruction is one of
   * these and in that case creates an appropriate object. In case the name is
   * of a different kind it returns the parameter <code>a_res</code>.
   *
   * The array instructions are:
   * <ul>
   *    <li>if_icmpeq,</li>
   *    <li>if_icmpge,</li>
   *    <li>if_icmpgt,</li>
   *    <li>if_icmple,</li>
   *    <li>if_icmplt,</li>
   *    <li>if_icmpne.</li>
   * </ul>
   *
   * @param an_ih an instruction handle of the target instruction
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private Instruction getIntCompIfInstruction(final InstructionHandle an_ih,
                                              final Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("if_icmpeq") == 0) {
      ires = new IF_ICMPEQ(an_ih);
    }
    if (getName().compareTo("if_icmpge") == 0) {
      ires = new IF_ICMPGE(an_ih);
    }
    if (getName().compareTo("if_icmpgt") == 0) {
      ires = new IF_ICMPGT(an_ih);
    }
    if (getName().compareTo("if_icmple") == 0) {
      ires = new IF_ICMPLE(an_ih);
    }
    if (getName().compareTo("if_icmplt") == 0) {
      ires = new IF_ICMPLT(an_ih);
    }
    if (getName().compareTo("if_icmpne") == 0) {
      ires = new IF_ICMPNE(an_ih);
    }
    return ires;
  }

  /**
   * This method creates the objects that represent if instructions that compare
   * with integer 0. It checks if the name of the current instruction is one of
   * these and in that case creates an appropriate object. In case the name is
   * of a different kind it returns the parameter <code>a_res</code>.
   *
   * The array instructions are:
   * <ul>
   *    <li>ifeq,</li>
   *    <li>ifge,</li>
   *    <li>ifgt,</li>
   *    <li>ifle,</li>
   *    <li>iflt,</li>
   *    <li>ifne.</li>
   * </ul>
   *
   * @param an_ih an instruction handle of the target instruction
   * @param a_res a helper value returned in case the current instruction is
   *   not in the current set
   * @return the object that represents the current instruction or res in
   *   case the current instruction is not in the current set
   */
  private Instruction getZeroCompIfInstruction(final InstructionHandle an_ih,
                                               final Instruction a_res) {
    Instruction ires = a_res;
    if (getName().compareTo("ifeq") == 0) {
      ires = new IFEQ(an_ih);
    }
    if (getName().compareTo("ifge") == 0) {
      ires = new IFGE(an_ih);
    }
    if (getName().compareTo("ifgt") == 0) {
      ires = new IFGT(an_ih);
    }
    if (getName().compareTo("ifle") == 0) {
      ires = new IFLE(an_ih);
    }
    if (getName().compareTo("iflt") == 0) {
      ires = new IFLT(an_ih);
    }
    if (getName().compareTo("ifne") == 0) {
      ires = new IFNE(an_ih);
    }
    return ires;
  }

  /**
   * Jump instruction requires an instruction number of
   * its target as a parameter. Note that the {@link BranchInstruction}
   * has only one target.
   *
   * @param an_ins_list an instruction list with the jump instruction
   * @param an_ins the jump instruction to set the target for
   * @throws UmbraException when the jump instruction has improper target
   * @see umbra.instructions.ast.BytecodeLineController#setTarget(
   *                            org.apache.bcel.generic.InstructionList,
   *                            org.apache.bcel.generic.Instruction)
   */
  public final void setTarget(final InstructionList an_ins_list,
                              final Instruction an_ins) throws UmbraException {
    int i = 0;
    i = getInd();
    InstructionHandle iha = null;
    iha = an_ins_list.findHandle(i);
    if (iha == null) {
      throw new UmbraException();
    }
    ((BranchInstruction)an_ins).setTarget(iha);
  }
}
