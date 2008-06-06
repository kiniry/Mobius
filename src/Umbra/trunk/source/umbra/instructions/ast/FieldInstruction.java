/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import org.apache.bcel.generic.GETFIELD;
import org.apache.bcel.generic.GETSTATIC;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.PUTFIELD;
import org.apache.bcel.generic.PUTSTATIC;

import umbra.instructions.InstructionParser;
import umbra.lib.BytecodeStrings;


/**
 * This class handles the creation and correctness for instructions to store and
 * load field values. These instructions are:
 * <ul>
 *   <li>getfield,</li>
 *   <li>getstatic,</li>
 *   <li>putfield,</li>
 *   <li>putstatic.</li>
 * </ul>
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class FieldInstruction extends StringInstruction {

  /**
   * This creates an instance of an instruction
   * named as <code>a_name</code> in a line the text of which is
   * <code>a_line_text</code>. Currently it just calls the constructor of the
   * superclass.
   *
   * @param a_line_text the line text of the instruction
   * @param a_name the mnemonic name of the instruction
   * @see InstructionLineController#InstructionLineController(String, String)
   */
  public FieldInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }

  /**
   * This method returns the array of field instructions mnemonics.
   *
   * @return the array of the handled mnemonics
   * @see InstructionLineController#getMnemonics()
   */
  public static /*@ non_null @*/ String[] getMnemonics() {
    return BytecodeStrings.FIELD_INS;
  }

  /**
   * Field instruction line is correct if it has two parameters. The first one
   * is the name of the field and the second is the descriptor of the field.
   * The precise format is:
   *    whitespase number : whitespace mnemonic whitespace fieldname
   *    typedescriptor whitespace ( whitespace number whitespace ) whitespace
   *    endline
   *
   * @return <code>true</code> when the syntax of the instruction line is
   *         correct
   * @see InstructionLineController#correct()
   */
  public final boolean correct() {
    boolean res = true;
    final InstructionParser parser = getParser();
    res = parseTillMnemonic(); //parse up to mnemonic
    res = res && (parser.swallowMnemonic(BytecodeStrings.FIELD_INS) >= 0);
                           //mnemonic
    res = res && parser.swallowWhitespace(); //whitespace before the method name
    res = res && parser.swallowFieldName(); // field name
    res = res && parser.swallowWhitespace(); //whitespace before the field type
    res = res && parser.swallowFieldType();
    res = res && parser.swallowWhitespace(); //whitespace before the number
    res = res && numberWithDelimiters(parser);
    res = res && !parser.swallowWhitespace();
    return res;
  }

  /**
   * This method, based on the value of the the mnemonic
   * name, creates a new BCEL instruction
   * object for a field access instruction. It computes the index parameter
   * of the instruction before the instruction is constructed. The method can
   * construct one of the instructions:
   * <ul>
   *   <li>getfield,</li>
   *   <li>getstatic,</li>
   *   <li>putfield,</li>
   *   <li>putstatic.</li>
   * </ul>
   * This method also checks the syntactical correctness of the current
   * instruction line.
   *
   * @return the freshly constructed BCEL instruction or <code>null</code>
   *         in case the instruction is not a field access instruction and
   *         in case the instruction line is incorrect
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {
    int index;

    final boolean isOK = correct();
    Instruction res = null;
    if (isOK) {
      index = getInd();
      if (getName().compareTo("getfield") == 0) {
        res = new GETFIELD(index);
      }
      if (getName().compareTo("getstatic") == 0) {
        res = new GETSTATIC(index);
      }
      if (getName().compareTo("putfield") == 0) {
        res = new PUTFIELD(index);
      }
      if (getName().compareTo("putstatic") == 0) {
        res = new PUTSTATIC(index);
      }
    }
    return res;
  }
}
