/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import org.apache.bcel.generic.INVOKESPECIAL;
import org.apache.bcel.generic.INVOKESTATIC;
import org.apache.bcel.generic.INVOKEVIRTUAL;
import org.apache.bcel.generic.Instruction;

import umbra.instructions.InstructionParser;
import umbra.lib.BytecodeStrings;


/**
 * This class handles the creation and correctness for invoke instructions. The
 * invoke instructions are:
 * <ul>
 *   <li>invokeinterface,</li>
 *   <li>invokespecial,</li>
 *   <li>invokestatic,</li>
 *   <li>invokevirtual.</li>
 * </ul>
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class InvokeInstruction extends StringInstruction {

  /**
   * This creates an instance of an instruction
   * named as <code>a_name</code> in a line the text of which is
   * <code>a_line_text</code>. Currently it just calls the constructor of the
   * superclass.
   *
   * @param a_line_text the string representation of the line text
   * @param a_name the mnemonic name of the instruction
   * @see InstructionLineController#InstructionLineController(String, String)
   */
  public InvokeInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }

  /**
   * This method returns the array of invoke instructions mnemonics.
   *
   * @return the array of the handled mnemonics
   * @see InstructionLineController#getMnemonics()
   */
  public static /*@ non_null @*/ String[] getMnemonics() {
    return BytecodeStrings.INVOKE_INS;
  }

  /**
   * Invoke instruction line is correct if its parameter
   * contains class name at the beginning and a number in ()
   * at the end.
   *    whitespase number : whitespace mnemonic whitespace methodname
   *    whitespace ( whitespace number whitespace )
   *    [ whitespace number whitespace number ] whitespace lineend
   * where the text between [] is optional and occurs only when the
   * mnemonic is "invokeinterface". Additionally the final number
   * parameter should always be 0.
   *
   * @return <code>true</code> when the syntax of the instruction line is
   *         correct
   * @see InstructionLineController#correct()
   */
  public final boolean correct() {
    boolean res = true;
    final InstructionParser parser = getParser();
    res = parseTillMnemonic(); //parse up to mnemonic
    res = res && (parser.swallowMnemonic(BytecodeStrings.INVOKE_INS) >= 0);
                           //mnemonic
    res = res && parser.swallowWhitespace(); //whitespace before the method name
    res = res && parser.swallowMethodReference(); // method name
    res = res && parser.swallowWhitespace(); //whitespace before the number
    res = res && numberWithDelimiters(parser); // number
    if (res && parser.getMnemonic() == BytecodeStrings.INVOKEINTERFACE_NO) {
      res = res && invokeinterfaceParams(parser);
    }
    res = res && !parser.swallowWhitespace();
    return res;
  }


  /**
   * This method tries to parse additional optional parameters of the
   * invokeinterface instruction. The precise format is:
   *    whitespace number whitespace number
   * Additionally, the second number must be 0;
   *
   * @param a_parser the parser which is to parse the parameters
   * @return <code>true</code> when the syntax of the parameters is
   *   correct
   */
  private boolean invokeinterfaceParams(final InstructionParser a_parser) {
    boolean res = a_parser.swallowWhitespace();
    res = res && a_parser.swallowNumber();
    res = res && a_parser.swallowWhitespace();
    res = res && a_parser.swallowNumber();
    res = res && (a_parser.getResult() == 0);
    return res;
  }

  /**
   * This method, based on the value of the the mnemonic
   * name, creates a new BCEL instruction
   * object for an invoke instruction. It computes the index parameter
   * of the instruction before the instruction is constructed. The method can
   * construct one of the instructions:
   * <ul>
   *   <li>invokeinterface,</li>
   *   <li>invokespecial,</li>
   *   <li>invokestatic,</li>
   *   <li>invokevirtual.</li>
   * </ul>
   * This method also checks the syntactical correctness of the current
   * instruction line.
   *
   * @return the freshly constructed BCEL instruction or <code>null</code>
   *         in case the instruction is not an invoke instruction and in case
   *         the line is incorrect
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {
    int index;
    index = getInd();

    if (!correct())
      return null;
    Instruction res = null;
    if (getName().compareTo("invokeinterface") == 0) {
      res = new INVOKESPECIAL(index);
    }
    if (getName().compareTo("invokespecial") == 0) {
      res = new INVOKESPECIAL(index);
    }
    if (getName().compareTo("invokestatic") == 0) {
      res = new INVOKESTATIC(index);
    }
    if (getName().compareTo("invokevirtual") == 0) {
      res = new INVOKEVIRTUAL(index);
    }

    return res;

  }
}
