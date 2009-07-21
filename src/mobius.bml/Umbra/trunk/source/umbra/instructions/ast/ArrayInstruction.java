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

import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.NEWARRAY;
import org.apache.bcel.generic.Type;

import umbra.instructions.InstructionParser;
import umbra.lib.BytecodeStrings;



/**
 * This class handles the creation and correctness for the instruction to
 * create new arrays of primitive types (newarray).
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class ArrayInstruction extends StringInstruction {

  /**
   * The types of the bytecode types used for the creation of
   * array instructions. It corresponds to the names
   * in the array {@link BytecodeStrings#PRIMITIVE_TYPE_NAMES}.
   */
  private static final Type[] TYPES = {Type.BOOLEAN, Type.CHAR, Type.FLOAT,
                                       Type.DOUBLE, Type.BYTE, Type.SHORT,
                                       Type.INT, Type.LONG};

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
  public ArrayInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }

  /**
   * This method returns the array of array instructions mnemonics.
   *
   * @return the array of the handled mnemonics
   * @see InstructionLineController#getMnemonics()
   */
  public static /*@ non_null @*/ String[] getMnemonics() {
    return BytecodeStrings.ARRAY_INS;
  }

  /**
   * This method parses the type name parameter of the current instruction.
   *
   * This method retrieves the type name value of the parameter of the
   * instruction in {@link BytecodeLineController#getMy_line_text()}. This
   * parameter is located after the mnemonic (with some whitespace inbetween).
   * The method assumes {@link BytecodeLineController#getMy_line_text()}
   * is correct.
   *
   * @return the value of the type name
   */
  private Type getType() {
    final InstructionParser parser = getParser();
    parser.resetParser();
    parser.seekDelimiter('<'); //  start of type
    parser.swallowWhitespace(); //whitespace before the type
    final int num = parser.swallowMnemonic(
                               BytecodeStrings.PRIMITIVE_TYPE_NAMES);
    return TYPES[num];
  }


  /**
   * This method, based on the value of the mnemonic
   * name, creates a new BCEL instruction
   * object for a push instruction. It computes the parameter of the
   * instruction before the instruction is constructed. The method can construct
   * one of the instructions:
   * <ul>
   *    <li>newarray.</li>
   * </ul>
   * This method also checks the syntactical correctness of the current
   * instruction line.
   *
   * @return the freshly constructed BCEL instruction or <code>null</code>
   *         in case the instruction is not a newarray instruction and
   *         in case the instruction line is incorrect
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {
    if (!correct()) {
      return null;
    }
    final byte r = getType().getType();
    if (getName().compareTo("newarray") == 0) {
      return new NEWARRAY(r);
    }
    return null;
  }


  /**
   * Array instruction line is correct if it has one parameter being the
   * type of the array elements. The exact definition of this kind of a line is
   * as follows:
   *    whitespase number : whitespace mnemonic whitespace
   *    &lt; whitespace typename whitespace &gt; whitespace lineend
   *
   * @return <code>true</code> when the syntax of the instruction line is
   *         correct
   * @see InstructionLineController#correct()
   */
  public final boolean correct() {
    boolean res = true;
    final InstructionParser parser = getParser();
    res = parseTillMnemonic(); //parse up to mnemonic
    res = res && (parser.swallowMnemonic(BytecodeStrings.ARRAY_INS) >= 0);
                           //mnemonic
    res = res && parser.swallowWhitespace(); //whitespace before the typename
    res = res && parser.swallowDelimiter('<'); //<
    res = res && parser.swallowWhitespace(); //whitespace before the typename
    res = res &&
       (parser.swallowMnemonic(BytecodeStrings.PRIMITIVE_TYPE_NAMES) >= 0);
                           // typename
    res = res && parser.swallowWhitespace(); //whitespace after the typename
    res = res && parser.swallowDelimiter('>'); //<
    res = res && !parser.swallowWhitespace();
    return res;
  }

  /**
   * This method changes all references to constant pool
   * from a "dirty" numbers to a "clean" ones in BCEL representation
   * of this instruction. <br> <br>
   *
   * This method does nothing, because array instruction does not have
   * any reference to constant pool entries.
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
