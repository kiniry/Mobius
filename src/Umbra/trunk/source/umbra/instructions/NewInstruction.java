/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import org.apache.bcel.generic.ANEWARRAY;
import org.apache.bcel.generic.CHECKCAST;
import org.apache.bcel.generic.INSTANCEOF;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.NEW;

import umbra.UmbraHelper;
import umbra.editor.parsing.BytecodeStrings;

/**
 * This class handles the creation and correctness for instructions to create
 * objects, check their types, and cast them, namely:
 *
 *<ul>
 *   <li>anewarray,</li>
 *   <li>checkcast,</li>
 *   <li>instanceof,</li>
 *   <li>new.</li>
 * </ul>
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class NewInstruction extends StringInstruction {

  /**
   * A position before which the '(' character cannot occur in a correct line.
   */
  private static final int LEFT_PAREN_FORBIDDEN_BOUND = 2;

  /**
   * A position before which the ')' character cannot occur in a correct line.
   */
  private static final int RIGHT_PAREN_FORBIDDEN_BOUND = 2;

  /**
   * A position before which the '<' character cannot occur in a correct line.
   */
  private static final int LESS_FORBIDDEN_BOUND = 2;

  /**
   * A position before which the '>' character cannot occur in a correct line.
   */
  private static final int GREATER_FORBIDDEN_BOUND = 2;

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
  public NewInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }


  /**
   * New instruction line is correct if it has one parameter that is a class
   * name in <> and another one that is a number in (). The presise format is:
   *    whitespase number : whitespace mnemonic whitespace
   *    &lt; whitespace classname whitespace &gt; whitespace
   *    ( whitespace number whitespace ) whitespace lineend
   *
   * @return <code>true</code> when the syntax of the instruction line is
   *         correct
   * @see InstructionLineController#correct()
   */
  public final boolean correct() {
    boolean res = true;
    final InstructionParser parser = getParser();
    res = parseTillMnemonic(); //parse up to mnemonic
    res = res && (parser.swallowMnemonic(BytecodeStrings.NEW_INS) >= 0);
                           //mnemonic
    res = res && parser.swallowWhitespace(); //whitespace before the classname
    res = res && classnameWithDelimiters(parser);
    res = res && parser.swallowWhitespace();
    res = res && numberWithDelimiters(parser);
    res = res && !parser.swallowWhitespace();
    return res;
  }


  private boolean numberWithDelimiters(InstructionParser parser) {
    boolean res = true;
    res = res && parser.swallowDelimiter('('); // (
    res = res && parser.swallowWhitespace();
    res = res && parser.swallowNumber(); // number
    res = res && parser.swallowDelimiter(')'); // )
    res = res && parser.swallowWhitespace();
    return res;
  }


  private boolean classnameWithDelimiters(InstructionParser parser) {
    boolean res = true;
    res = res && parser.swallowDelimiter('<'); // <
    res = res && parser.swallowWhitespace();
    if (res)
      res = res && parser.swallowClassname(); //class name
    res = res && parser.swallowWhitespace();
    res = res && parser.swallowDelimiter('>'); // >
    return res;
  }


  /**
   * This method, based on the value of the field
   * {@ref InstructionLineController#my_name}, creates a new BCEL instruction
   * object for a new-like instruction. It computes the index parameter
   * of the instruction before the instruction is constructed. The method can
   * construct one of the instructions:
   * <ul>
   *   <li>anewarray,</li>
   *   <li>checkcast,</li>
   *   <li>instanceof,</li>
   *   <li>new.</li>
   * </ul>
   * This method also checks the syntactical correctness of the current
   * instruction line.
   *
   * @return the freshly constructed BCEL instruction or <code>null</code>
   *         in case the instruction is not a new-like instruction and in case
   *         the line is incorrect
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {
    int index;
    Instruction res = null;
    if (!correct())
      return null;
    index = getInd();
    if (getName().compareTo("anewarray") == 0) {
      res = new ANEWARRAY(index);
    }
    if (getName().compareTo("checkcast") == 0) {
      res = new CHECKCAST(index);
    }
    if (getName().compareTo("instanceof") == 0) {
      res = new INSTANCEOF(index);
    }
    if (getName().compareTo("new") == 0) {
      res = new NEW(index);
    }
    return res;
  }
}
