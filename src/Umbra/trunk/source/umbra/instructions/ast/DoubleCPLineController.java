/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import umbra.instructions.InstructionParser;
import umbra.lib.BytecodeStrings;

/**
 * This is a class that represents CONSTANT_Double_info constant
 * pool entry line controller.
 * 
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 */
public class DoubleCPLineController extends CPLineController {

  /**
   * This creates an instance of a bytecode line handle to handle
   * constant pool entry of the type CONSTANT_Double_info.
   *
   * @param a_line_text the string representation of the line text
   * @param an_entry_type the string "Double", ignored parameter
   * for compatibility with
   * {@link umbra.instructions.DispatchingAutomaton#callConstructor}
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public DoubleCPLineController(final String a_line_text, final String an_entry_type) {
    super(a_line_text, an_entry_type);
  }
  
  /**
   * This method returns the string "Double" which describes
   * CONSTANT_Double_info constant pool entry type handled by the
   * current class.
   * 
   * @return handled entry type
   */
  public static String getEntryType() {
    return BytecodeStrings.DOUBLE_CP_ENTRY_KEYWORD;
  }
  
  /**
   * The CONSTANT_Double_info constant pool entry line is correct if
   * it has format: <br> <br>
   * 
   * [ ]*const[ ]*&lt;ref&gt;[ ]*=[ ]*Double[ ]*&lt;fnum&gt;[ ]*;[ ]* <br> <br> 
   * where &lt;fnum&gt; is a floating point number in format specified in
   * "Textual Representation of Specifications" of "BML Reference Manual".
   * Additionally we check whether &lt;fnum&gt; is double number.
   * 
   * @return <code> true </code> when the syntax of constant pool
   * entry is correct
   * @see CPLineController#correct()
   */
  public final boolean correct() {
    boolean res = parseTillEntryType();
    InstructionParser my_parser = getParser();
    res = res && my_parser.swallowWhitespace();
    res = res && my_parser.swallowSingleMnemonic(BytecodeStrings.DOUBLE_CP_ENTRY_KEYWORD);
    res = res && my_parser.swallowWhitespace();
    res = res && my_parser.swallowFPNumber();
    if (my_parser.getFPResult() != null && my_parser.getFPResult().length() > 0) {
      if (my_parser.getFPResult().charAt(my_parser.getFPResult().length() - 1) == 'F' ||
        my_parser.getFPResult().charAt(my_parser.getFPResult().length() - 1) == 'f')
      return false;
    }
    res = res && my_parser.swallowWhitespace();
    res = res && my_parser.swallowDelimiter(';');
    res = res && !my_parser.swallowWhitespace();
    return res;
  }
  
  /**
   * This method parses the parameter of the current constant pool entry.
   *
   * This method retrieves the string representation of the parameter of the
   * constant pool entry in {@link BytecodeLineController#getMy_line_text()}.
   * This parameter is located after the constant pool entry keyword. The
   * method assumes {@link BytecodeLineController#getMy_line_text()} is correct.
   *
   * @return the string representation of the floating point parameter of the
   * constant pool entry
   */
  private String getParam() {
    parseTillEntryType();
    InstructionParser my_parser = getParser();
    my_parser.swallowWhitespace();
    my_parser.swallowSingleMnemonic(BytecodeStrings.DOUBLE_CP_ENTRY_KEYWORD);
    my_parser.swallowWhitespace();
    my_parser.swallowFPNumber();
    return my_parser.getFPResult();
  }

}
