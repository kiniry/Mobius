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

import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantLong;

import umbra.instructions.InstructionParser;
import umbra.lib.BytecodeStrings;

/**
 * This is a class that represents CONSTANT_Long_info constant
 * pool entry line controller.
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class LongCPLineController extends CPLineController {

  /**
   * This creates an instance of a bytecode line handle to handle
   * constant pool entry of the type CONSTANT_Long_info.
   *
   * @param a_line_text the string representation of the line text
   * @param an_entry_type the string "Long", ignored parameter
   * for compatibility with
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public LongCPLineController(final String a_line_text,
                              final String an_entry_type) {
    super(a_line_text, an_entry_type);
  }

  /**
   * This method returns the string "Long" which describes
   * CONSTANT_Long_info constant pool entry type handled by the
   * current class.
   *
   * @return handled entry type
   */
  public static String getEntryType() {
    return BytecodeStrings.LONG_CP_ENTRY_KEYWORD;
  }

  /**
   * The CONSTANT_Long_info constant pool entry line is correct if
   * it has format: <br> <br>
   *
   * [ ]*const[ ]*&lt;ref&gt;[ ]*=[ ]*Long[ ]*&lt;num&gt;[ ]*;[ ]* <br> <br>
   * where &lt;num&gt; is an long integer.
   *
   * @return <code> true </code> when the syntax of constant pool
   * entry is correct
   * @see CPLineController#correct()
   */
  public final boolean correct() {
    boolean res = parseTillEntryType();
    final InstructionParser my_parser = getParser();
    res = res && my_parser.swallowWhitespace();
    res = res && my_parser.swallowSingleMnemonic(BytecodeStrings.
                                                 LONG_CP_ENTRY_KEYWORD);
    res = res && my_parser.swallowWhitespace();
    res = res && my_parser.swallowLongNumber();
    res = res && my_parser.swallowWhitespace();
    res = res && my_parser.swallowDelimiter(';');
    res = res && !my_parser.swallowWhitespace();
    return res;
  }

  /**
   * This method parses the parameter of the current constant pool entry.
   *
   * This method retrieves the numerical value of the parameter of the
   * constant pool entry in {@link BytecodeLineController#getMy_line_text()}.
   * This parameter is located after the constant pool entry keyword. The
   * method assumes {@link BytecodeLineController#getMy_line_text()} is correct.
   *
   * @return the value of the floating point parameter of the constant pool
   * entry
   */
  private long getParam() {
    parseTillEntryType();
    final InstructionParser my_parser = getParser();
    my_parser.swallowWhitespace();
    my_parser.swallowSingleMnemonic(BytecodeStrings.INTEGER_CP_ENTRY_KEYWORD);
    my_parser.swallowWhitespace();
    my_parser.swallowLongNumber();
    return my_parser.getLongResult();
  }

  /**
   * Returns the link to the BCEL long constant represented by the current
   * line. If there is no such constant it creates the constant before
   * returning. Newly created constant should then be associated with BML
   * constant pool representation. <br> <br>
   *
   * @return a BCEL constant represented by the current line
   */
  public Constant getConstant() {
    if (getConstantAccessor() != null) return getConstantAccessor();
    setConstant(new ConstantLong(getParam()));
    return getConstantAccessor();
  }

  /**
   * This method changes references to constant pool entries from "dirty"
   * numbers to "clean" ones. <br>
   * The change has effect only in BCEL representation of constant pool and does
   * not affect internal Umbra representation. <br> <br>
   *
   * See {@link BytecodeController#recalculateCPNumbers()} for explantation of
   * "dirty" and "clean" numbers concepts. <br> <br>
   *
   * This method does nothing as long constant pool entries don't have any
   * references.
   *
   * @param a_map a hash map which maps "dirty" numbers to "clean" ones
   */
  public void updateReferences(final HashMap a_map) {

  }

}
