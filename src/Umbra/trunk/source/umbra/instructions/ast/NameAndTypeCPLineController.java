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
 * This is a class that represents CONSTANT_NameAndType_info constant
 * pool entry line controller.
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class NameAndTypeCPLineController extends CPLineController {

  /**
   * This creates an instance of a bytecode line handle to handle
   * constant pool entry of the type CONSTANT_NameAndType_info.
   *
   * @param a_line_text the string representation of the line text
   * @param an_entry_type the string "NameAndType", ignored parameter
   * for compatibility with
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public NameAndTypeCPLineController(final String a_line_text, final String an_entry_type) {
    super(a_line_text, an_entry_type);
  }
  
  /**
   * This method returns the string "NameAndType" which describes
   * CONSTANT_NameAndType_info constant pool entry type handled by the
   * current class.
   * 
   * @return handled entry type
   */
  public static String getEntryType() {
    return BytecodeStrings.NAME_AND_TYPE_CP_ENTRY_KEYWORD;
  }
  
  /**
   * The CONSTANT_NameAndType_info constant pool entry line is correct if
   * it has format: <br> <br>
   * 
   * [ ]*const[ ]*&lt;ref&gt;[ ]*=[ ]*NameAndType[ ]*&lt;ref&gt;.&lt;ref&gt;[ ]*;[ ]*
   * <br> <br>
   * 
   * where &lt;ref&gt; ::= #&lt;positive integer&gt;.
   * 
   * @return <code> true </code> when the syntax of constant pool
   * entry is correct
   * @see CPLineController#correct()
   */
  public final boolean correct() {
    boolean res = parseTillEntryType();
    InstructionParser my_parser = getParser();
    res = res && my_parser.swallowWhitespace();
    res = res &&my_parser.swallowSingleMnemonic(BytecodeStrings.NAME_AND_TYPE_CP_ENTRY_KEYWORD);
    res = res && my_parser.swallowWhitespace();
    res = res && my_parser.swallowDelimiter('#');
    res = res && my_parser.swallowCPReferenceNumber();
    res = res && my_parser.swallowDelimiter(':');
    res = res && my_parser.swallowDelimiter('#');
    res = res && my_parser.swallowCPReferenceNumber();
    res = res && my_parser.swallowWhitespace();
    res = res && my_parser.swallowDelimiter(';');
    res = res && !my_parser.swallowWhitespace();
    return res;
  }
  
  /**
  * This method retrieves the reference to the name string from the
  * CONSTANT_NameAndType_info constant pool entry in
  * {@link BytecodeLineController#getMy_line_text()}. This parameter
  * is located after the entry type keyword. 
  * The method assumes {@link BytecodeLineController#getMy_line_text()}
  * is correct.
  * 
  * @return reference to the name string referenced by constant pool entry
  */
  private int getNameReference() {
    parseTillEntryType();
    InstructionParser my_parser = getParser();
    my_parser.swallowWhitespace();
    my_parser.swallowSingleMnemonic(BytecodeStrings.INTERFACE_METHODREF_CP_ENTRY_KEYWORD);
    my_parser.swallowWhitespace();
    my_parser.swallowDelimiter('#');
    my_parser.swallowCPReferenceNumber();
    return my_parser.getResult();
  }
  
  /**
   * This method retrieves the reference to the type string from the
   * CONSTANT_NameAndType_info constant pool entry
   * in {@link BytecodeLineController#getMy_line_text()}. This parameter
   * is located after the first parameter (reference to the name string)
   * with dot in between.
   * The method assumes {@link BytecodeLineController#getMy_line_text()}
   * is correct. It also assumes that the internal parser state has not
   * been modified between the call to {@link #getNameReference()} and the call
   * of this method.
   * 
   * @return reference to the type string referenced by constant pool entry
   */
  private int getTypeReference() {
    InstructionParser my_parser = getParser();
    my_parser.swallowDelimiter('.');
    my_parser.swallowDelimiter('#');
    my_parser.swallowCPReferenceNumber();
    return my_parser.getResult();
  }
  
}
