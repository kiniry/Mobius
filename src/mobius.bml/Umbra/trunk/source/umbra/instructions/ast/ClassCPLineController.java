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

import umbra.lib.BytecodeStrings;
import umbra.lib.UmbraNoSuchConstantException;
import umbra.instructions.InstructionParser;
import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantClass;
import umbra.instructions.errors.NoSuchConstantError;

/**
 * This is a class that represents CONSTANT_Class_info constant
 * pool entry line controller.
 *
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class ClassCPLineController extends CPLineController {

  /**
   * This creates an instance of a bytecode line controller to handle
   * constant pool entry of the type CONSTANT_Class_info.
   *
   * @param a_line_text the string representation of the line text
   * @param an_entry_type the string "Class", ignored parameter
   * for compatibility with
   * {@link umbra.instructions.DispatchingAutomaton#callConstructor}
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public ClassCPLineController(final String a_line_text,
                               final String an_entry_type) {
    super(a_line_text, an_entry_type);
  }

  /**
   * This method returns the string "Class" which describes
   * CONSTANT_Class_info constant pool entry type handled by the
   * current class.
   *
   * @return handled entry type
   */
  public static String getEntryType() {
    return BytecodeStrings.CLASS_CP_ENTRY_KEYWORD;
  }

  /**
   * The CONSTANT_Class_info constant pool entry line is correct if
   * it has format: <br> <br>
   *
   * [ ]*const[ ]*&lt;ref&gt;[ ]*=[ ]*Class[ ]*&lt;ref&gt;[ ]*;[ ]* <br> <br>
   *
   * where &lt;ref&gt; ::= #&lt;positive integer&gt;.
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
                                                 CLASS_CP_ENTRY_KEYWORD);
    res = res && my_parser.swallowWhitespace();
    res = res && my_parser.swallowDelimiter('#');
    res = res && my_parser.swallowCPReferenceNumber();
    res = res && my_parser.swallowWhitespace();
    res = res && my_parser.swallowDelimiter(';');
    res = res && !my_parser.swallowWhitespace();
    return res;
  }

  /**
  * This method retrieves the reference to the utf8 CP entry
  * containing name of the class represented by the class constant
  * pool entry in {@link BytecodeLineController#getMy_line_text()}.
  * This parameter is located after the entry type keyword.
  * The method assumes {@link BytecodeLineController#getMy_line_text()}
  * is correct.
  *
  * @return reference to the utf8 constant pool entry referenced by
  * class constant pool entry
  */
  private int getClassReference() {
    parseTillEntryType();
    final InstructionParser my_parser = getParser();
    my_parser.swallowWhitespace();
    my_parser.swallowSingleMnemonic(BytecodeStrings.CLASS_CP_ENTRY_KEYWORD);
    my_parser.swallowWhitespace();
    my_parser.swallowDelimiter('#');
    my_parser.swallowCPReferenceNumber();
    return my_parser.getResult();
  }

  /**
   * Returns the link to the BCEL class constant represented by the current
   * line. If there is no such constant it creates the constant before
   * returning. Newly created constant should then be associated with BML
   * constant pool representation. <br> <br>
   *
   * The constant reference number set for the newly created constant is
   * the "dirty" number. It should be changed to "clean" number in
   * {@link umbra.instructions.BytecodeController#recalculateCPNumbers(
   * org.apache.bcel.classfile.JavaClass)}.
   * <br> <br>
   *
   * For explantation of "dirty" and "clean" number concepts see
   * {@link umbra.instructions.BytecodeController#recalculateCPNumbers(
   * org.apache.bcel.classfile.JavaClass)}.
   *
   * @return a BCEL constant represented by the current line
   */
  public Constant getConstant() {
    if (getConstantAccessor() != null) return getConstantAccessor();
    setConstant(new ConstantClass(getClassReference()));
    return getConstantAccessor();
  }

  /**
   * This method changes reference to the utf8 CP entry referenced by this
   * constant from a "dirty" number to a "clean" one in BCEL representation
   * of constant pool. <br> <br>
   *
   * See {@link umbra.instructions.BytecodeController#recalculateCPNumbers(
   * org.apache.bcel.classfile.JavaClass)} for explantation of
   * "dirty" and "clean" numbers concepts. <br> <br>
   *
   * @param a_map a hash map which maps "dirty" numbers to "clean" ones
   */
  public void updateReferences(final HashMap a_map) {
    ((ConstantClass) getConstantAccessor()).setNameIndex((Integer)
      dirtyToClean(a_map, getClassReference()));
  }

  /**
   * This method checks if there are any references to non-existing
   * constant from this constant, and throws exception in such case.
   *
   * @param a_set a set of constant numbers in textual representation
   * of bytecode
   * @throws UmbraNoSuchConstantException if there is reference from
   * this constant to non-existing constant
   */
  public void checkCorrectness(final HashSet a_set)
    throws UmbraNoSuchConstantException {
    if (!a_set.contains(getClassReference())) {
      final NoSuchConstantError an_error = new NoSuchConstantError();
      an_error.addLine(this);
      an_error.addNumber(getClassReference());
      throw new UmbraNoSuchConstantException(an_error);
    }
  }

}
