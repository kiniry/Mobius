/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import java.util.HashMap;
import java.util.HashSet;

import umbra.instructions.InstructionParser;
import umbra.instructions.errors.NoSuchConstantError;
import umbra.lib.UmbraNoSuchConstantException;


/**
 * This is abstract class for all instructions with a number as a
 * parameter.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class NumInstruction extends MultiInstruction {

  /**
   * The constant to indicate one that the instruction has one parameter.
   */
  private static final int PARAMS_ONE = 1;

  /**
   * The constant to indicate one that the instruction has two parameters.
   */
  private static final int PARAMS_TWO = 2;

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
  public NumInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }

  /**
   * The method checks if the instruction <code>an_instr</code> occurs
   * correctly formatted in the line <code>a_line</code>.
   *
   * The line is correct when it has the format
   *    whitespase number : whitespace mnemonic whitespace a_char_label
   *    whitespace number whitespace [number] whitespace lineend
   *
   * @param a_line a bytecode line with all the whitespace stripped
   * @param an_instr an instruction text to be checked
   * @param a_char_label the character which delimits the number
   * @return -1 when we know that the syntax is wrong, 1 when we know the
   *         syntax is OK, 0 when we do not know, but we must search further
   */
  protected int checkInstructionWithNumber(final String a_line,
                                           final String an_instr,
                                           final char a_char_label) {
    boolean res = true;
    final InstructionParser parser = getParser();
    res = parseTillMnemonic(); //parse up to mnemonic
    final String [] inv = {an_instr};
    res = res && (parser.swallowMnemonic(inv) >= 0); //mnemonic
    res = res && parser.swallowWhitespace(); //whitespace before the delimiter
    res = res && parser.swallowDelimiter(a_char_label);
    res = res && parser.swallowWhitespace(); //whitespace after the delimiter
    if (res)
      return checkNoParameters(parser);
    else
      return -1;
  }

  /**
   * This method counts the number of parameters in the instruction parsed
   * by <code>a_parser</code>.
   *
   * We assume the index of the parser is situated so that the first number
   * is about to be read (with no whitespace before that). We try then to
   * read the first number and in case there is still something in the line
   * the second number.
   *
   * @param a_parser the parser which parses the analysed string
   * @return 1, 2 mean one and two parameters resp., in other cases -1 is
   *   returned
   */
  private int checkNoParameters(final InstructionParser a_parser) {
    boolean res = true;
    int parnum = 0;
    res = res && a_parser.swallowNumber(); // number
    if (res)
      parnum = PARAMS_ONE;
    else
      return -1;
    res = res && a_parser.swallowWhitespace(); //whitespace between the numbers
    if (!res) return parnum;
    res = res && a_parser.swallowNumber(); // second optional number
    res = res && !a_parser.swallowWhitespace();
    if (res)
      parnum = PARAMS_TWO;
    else
      parnum = -1;
    return parnum;
  }

  /**
   * This method changes all references to constant pool
   * from a "dirty" numbers to a "clean" ones in BCEL representation
   * of this instruction. <br> <br>
   *
   * This method does nothing, because this class represents instructions
   * that do not have any reference to constant pool entries.
   *
   * @param a_map a hash map which maps "dirty" numbers to "clean" ones
   * @param a_pos position in method
   */
  public void updateReferences(final HashMap a_map, final int a_pos) {

  }

  /**
   * This method checks if there are any references to non-existing
   * constant from this instruction, and throws exception in such case.
   * <br> <br>
   * This method does nothing, because this class represents instructions
   * that do not have any reference to constant pool entries.
   *
   * @param a_set a set of constant numbers in textual representation
   * of bytecode
   */
  public void checkCorrectness(final HashSet a_set) {

  }

}
