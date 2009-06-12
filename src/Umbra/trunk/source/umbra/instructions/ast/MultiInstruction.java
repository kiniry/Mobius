/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import java.util.HashMap;
import java.util.HashSet;

import org.apache.bcel.generic.MethodGen;

import annot.bcclass.BCMethod;

import umbra.UmbraPlugin;
import umbra.instructions.InstructionParser;
import umbra.instructions.errors.NoSuchConstantError;
import umbra.lib.UmbraNoSuchConstantException;
import umbra.lib.UmbraException;

/**
 * This is abstract class for all instructions with at least one
 * parameter.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class MultiInstruction extends InstructionLineController {

  /**
   * Stores parameter of current instruction.
   */
  private int my_ind;

  /**
   * Has value true if my_ind should be used instead of parsing parameter
   * from textual representation of this line.
   */
  private boolean my_use_stored_ind;

  /**
   * If there is no parameter has value false, true otherwise. The getInd()
   * should be called before for has_ind to have meaningfull value.
   */
  private boolean my_has_ind;

  /**
   * This creates an instance of an instruction
   * named as <code>a_name</code> at the line number
   * <code>a_line_text</code>. Currently it just calls the constructor of the
   * superclass.
   *
   * @param a_line_text the string representation of the line text
   * @param a_name the mnemonic name of the instruction
   * @see InstructionLineController#InstructionLineController(String, String)
   */
  public MultiInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
    my_use_stored_ind = false;
  }

  /**
   * This method checks if the last parenthesis in the given string
   * contains only digits.
   *
   * @param a_line_text the string to check
   * @return <code>true</code> when the last parenthesis contains only digits,
   *   <code>false</code> otherwise
   */
  public static /*@ pure @*/ boolean onlyDigitsInParen(
              final /*@ non_null @*/ String a_line_text) {
    for (int i = a_line_text.lastIndexOf("(") + 1;
         i < a_line_text.lastIndexOf(")"); i++) {
      if (!Character.isDigit(a_line_text.charAt(i))) {
        return false;
      }
    }
    return true;
  }

  /**
   * The method returns the number between the final parenthesis in the given
   * string. It assumes that the string between the parenthesis indeed
   * represents a number.
   *
   * @param a_line_text a string to extract the number from
   * @return the extracted number
   */
  public static /*@ pure @*/ int getNumInParen(
         final /*@ non_null @*/ String a_line_text) {
    final String numstring = a_line_text.substring(
      a_line_text.lastIndexOf("(") + 1, a_line_text.lastIndexOf(")"));
    return Integer.parseInt(numstring);
  }

  /**
   * This method parses the parameter of the current instruction.
   *
   * The default behaviour is that it parses the content of the final
   * parenthesis in the instruction with a numeric argument. It checks if the
   * argument is indeed the number and in that case it returns the number. In
   * case the argument is not a number, the method returns 0. It also issues
   * some logging information when the line has incorrect format.
   *
   * @return the parsed number or 0 in case the number cannot be parsed
   */
  protected int getInd() {
    if (my_use_stored_ind) return my_ind;
    final String my_line_text = getMy_line_text();
    if (my_line_text.lastIndexOf("(") >= my_line_text.lastIndexOf(")")) {
      UmbraPlugin.messagelog("A line is incorrect\n" +
                             "line content: >" + my_line_text + "<\n" +
                             "wrong content:" +
                             my_line_text.lastIndexOf("(") + " " +
                             my_line_text.lastIndexOf(")"));
    } else {
      if (MultiInstruction.onlyDigitsInParen(my_line_text)) {
        my_has_ind = true;
        return MultiInstruction.getNumInParen(my_line_text);
      }
    }
    my_has_ind = false;
    return 0;
  }

  /**
   * This method tries to parse a number in (). The precise format is:
   *    ( whitespace number whitespace )
   *
   * @param a_parser the parser which is to parse the number
   * @return <code>true</code> when the syntax of the number is
   *         correct
   */
  protected boolean numberWithDelimiters(final InstructionParser a_parser) {
    boolean res = true;
    res = res && a_parser.swallowDelimiter('('); // (
    res = res && a_parser.swallowWhitespace();
    res = res && a_parser.swallowNumber(); // number
    res = res && a_parser.swallowDelimiter(')'); // )
    return res;
  }

  /**
   * This method changes all references to constant pool
   * from a "dirty" numbers to a "clean" ones in BCEL representation
   * of this instruction. <br> <br>
   *
   * See {@link BytecodeController#recalculateCPNumbers(JavaClass a_jc)}
   * for explantation of "dirty" and "clean" numbers concepts. <br> <br>
   *
   * TODO (Umbra) this method breaks jump instructions <br> <br>
   *
   * @param a_map a hash map which maps "dirty" numbers to "clean" ones
   * @param a_pos position in method
   * @throws UmbraException in case the deletion of old method handle failed
   */
  public void updateReferences(final HashMap a_map, final int a_pos)
    throws UmbraException {
    if (!correct()) return;
    getInd();
    if (!my_has_ind) return;

    my_ind = (Integer) dirtyToClean(a_map, getInd());
    my_use_stored_ind = true;
    //int a_pos = this.getList().
    final int pos = getNoInMethod();

    dispose();
    makeHandleForPosition(getMethod(), pos);

    my_use_stored_ind = false;
  }

  /**
   * This method checks if there are any references to non-existing
   * constant from this instruction, and throws exception in such case.
   *
   * @param a_set a set of constant numbers in textual representation
   * of bytecode
   * @throws UmbraNoSuchConstantException if there is reference from
   * this instruction to non-existing constant
   */
  public void checkCorrectness(final HashSet a_set)
    throws UmbraNoSuchConstantException {
    if (!correct()) return;
    getInd();
    if (!my_has_ind) return;
    if (!a_set.contains(getInd())) {
      final NoSuchConstantError an_error = new NoSuchConstantError();
      an_error.addLine(this);
      an_error.addNumber(getInd());
      throw new UmbraNoSuchConstantException(an_error);
    }
  }

  /**
   * Prints BCEL instruction representation.
   * For debug use only.
   */
  @SuppressWarnings("unused")
  private void bcelDump() {
    final BCMethod mg = this.getMethod();
    for (int i = 0; i < mg.getInstructions().size(); i++) {
      final org.apache.bcel.generic.Instruction in =
        mg.getInstructions().getInstructions()[i];
      System.err.println(in.toString());
    }
  }

}
