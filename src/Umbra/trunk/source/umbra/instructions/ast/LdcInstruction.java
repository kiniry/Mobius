/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.LDC;
import org.apache.bcel.generic.LDC2_W;
import org.apache.bcel.generic.LDC_W;

import umbra.instructions.InstructionParser;
import umbra.lib.BytecodeStrings;


/**
 * This class is related to some subset of instructions
 * depending on parameters. It redefines some crucial while
 * handling with single instruction methods(correctness, getting handle).
 * These instruction are dealing with long data.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class LdcInstruction extends OtherInstruction {

  /**
   * This creates an instance of an instruction
   * named as <code>a_name</code> in a line the text of which is
   * <code>a_line_text</code>. Currently it just calls the constructor of the
   * superclass.
   *
   * @param a_line_text the line number of the instruction
   * @param a_name the mnemonic name of the instruction
   * @see InstructionLineController#InstructionLineController(String, String)
   */
  public LdcInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }

  /**
   * This method returns the array of ldc instructions mnemonics.
   *
   * @return the array of the handled mnemonics
   * @see InstructionLineController#getMnemonics()
   */
  public static /*@ non_null @*/ String[] getMnemonics() {
    return BytecodeStrings.LDC_INS;
  }

  /**
   * This method, based on the value of the mnemonic
   * name, creates a new BCEL instruction
   * object for an LCD instruction, i.e.:
   * <ul>
   *    <li>ldc,</li>
   *    <li>ldc_w,</li>
   *    <li>ldc2_w.</li>
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
    int index;

    if (!correct()) {
      System.err.println("incorrect: " + getLineContent());
      return null;
    }
    Instruction res = null;
    index = getInd();
    if (getName().compareTo("ldc") == 0) {
      res = new LDC(index);
    }
    if (getName().compareTo("ldc_w") == 0) {
      res = new LDC_W(index);
    }
    if (getName().compareTo("ldc2_w") == 0) {
      res = new LDC2_W(index);
    }
    return res;
  }

  /**
   * LDC instruction line is correct if it has one parameter that is a string
   * enclosed by two " and another one that is a number in (). The precise
   * format is:
   *    whitespase number : whitespace mnemonic whitespace
   *    " string " whitespace ( whitespace number whitespace )
   *    whitespace lineend
   * or
   *    whitespase number : whitespace mnemonic whitespace
   *    number whitespace ( whitespace number whitespace )
   *    whitespace lineend
   *
   * @return <code>true</code> when the syntax of the instruction line is
   *         correct
   * @see InstructionLineController#correct()
   */
  public final boolean correct() {
    boolean res = true;
    final InstructionParser parser = getParser();
    res = parseTillMnemonic(); //parse up to mnemonic
    res = res && (parser.swallowMnemonic(BytecodeStrings.LDC_INS) >= 0);
                           //mnemonic
    res = res && parser.swallowWhitespace(); //whitespace before the string
    if (parser.getLine().charAt(parser.getIndex()) == '\"') {
      res = res && stringWithDelimiters(parser);
    } else {
      /* XXX (Umbra) check whether other classes can take
       * floating point parameters (and change from swallowNumber()
       * to swallowFPNumber() is needed)
       */
      res = res && parser.swallowFPNumber();
    }
    res = res && parser.swallowWhitespace();
    res = res && numberWithDelimiters(parser);
    res = res && !parser.swallowWhitespace();
    return res;
  }

  /**
   * This method tries to parse a string in ". The precise format is:
   *    " string "
   *
   * @param a_parser the parser which is to parse the string
   * @return <code>true</code> when the syntax of the string is
   *         correct
   */
  private boolean stringWithDelimiters(final InstructionParser a_parser) {
    boolean res = true;
    res = res && a_parser.swallowDelimiter('"'); // (
    res = res && a_parser.swallowString(); // number
    res = res && a_parser.swallowDelimiter('"'); // )
    res = res && a_parser.swallowWhitespace();
    return res;
  }

}
