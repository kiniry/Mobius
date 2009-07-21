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

import umbra.instructions.InstructionParser;
import umbra.lib.BytecodeStrings;
import umbra.lib.UmbraNoSuchConstantException;

import org.apache.bcel.classfile.Constant;


/**
 * This is a class for lines in bytecode files inside the constant pool.
 *
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public abstract class CPLineController extends BytecodeLineController {

  /**
   * This array contains the classes which are able to handle constant
   * pool entries.
   */
  public static final Class [] CP_CLASS_HIERARCHY =  {
    ClassCPLineController.class,
    FieldrefCPLineController.class,
    MethodrefCPLineController.class,
    InterfaceMethodrefCPLineController.class,
    StringCPLineController.class,
    IntegerCPLineController.class,
    FloatCPLineController.class,
    LongCPLineController.class,
    DoubleCPLineController.class,
    NameAndTypeCPLineController.class,
    Utf8CPLineController.class};

  /**
   * The number of the constant in the constant pool which is represented
   * by the current line.
   */
  private int my_constno;

  /**
   * Link to the BCEL constant represented by this line.
   */
  private Constant my_constant;

  /**
   * This creates an instance of a bytecode line handle to handle
   * constant pool entry.
   *
   * @param a_line_text the string representation of the line text
   * @param an_entry_type the entry type handled by the current class,
   * ignored parameter for compatibility with
   * {@link umbra.instructions.DispatchingAutomaton#callConstructor}
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public CPLineController(final String a_line_text,
                          final String an_entry_type) {
    super(a_line_text);
  }

  /**
   * This method returns the entry type handled by the current class.
   * It should be redefined in each subclass.
   *
   * @return handled entry type
   */
  public static String getEntryType() {
    return null;
  }

  /**
   * This method checks if the particular line can be a constant pool line.
   *
   * @param a_line the string to check if it can be a constant pool line
   * @return <code>true</code> when the string can be a constant pool line,
   *   <code>false</code> otherwise
   */
  public static boolean isCPLineStart(final String a_line) {
    final String line = a_line.replaceAll("[ \t]+", " ");
    System.err.println(line);
    return line.startsWith(BytecodeStrings.CP_ENTRY_PREFIX[0]) ||
    line.startsWith(BytecodeStrings.CP_ENTRY_PREFIX[1]);
  }

  /**
   * This method is redefined in each subclass. It is used to check
   * syntactic correctness of the constant pool entry line.
   *
   * @return true if the constant pool entry is correct
   */
  public boolean correct() {
    return true;
  }


  /**
   * This method does the initial preparsing of the constant pool
   * entry line. This is the helper method which parses the common
   * part of each constant pool entry line: <br> <br>
   *
   *   [ ]*const[ ]*#&lt;ref&gt;[ ]*=[ ]* <br> <br>
   *
   * where &lt;ref&gt; ::= #&lt;positive integer&gt;. It initializes the parser
   * if hasn't been already initialized.
   *
   * @return <code>true</code> when all the parsing is done sucessfully,
   *   <code>false</code> in case the initial portion of the line is not of
   *   the required form
   */
  protected boolean parseTillEntryType()  {
    InstructionParser my_parser = getParser();
    if (my_parser == null) {
      my_parser = new InstructionParser(getLineContent());
    }
    my_parser.resetParser();
    boolean res = true;
    res = res && my_parser.swallowWhitespace();
    res = res && my_parser.swallowGivenWord(BytecodeStrings.JAVA_KEYWORDS[
                                 BytecodeStrings.CP_ENTRY_KEYWORD_POS]);
    res = res && my_parser.swallowWhitespace();
    res = res && my_parser.swallowDelimiter('#');
    res = res && my_parser.swallowCPReferenceNumber();
    if (res) {
      my_constno = my_parser.getResult();
    }
    res = res && my_parser.swallowWhitespace();
    res = res && my_parser.swallowDelimiter('=');
    return res;
  }

  /**
   * Returns the number of the constant in the constant pool.
   *
   * @return the number of the constant in the constant pool
   */
  public int getConstantNumber() {
    return my_constno;
  }

  /**
   * Sets the link to the BCEL constant represented by the current line.
   *
   * @param a_constant a BCEL constant represented by the current line
   */
  public void setConstant(final Constant a_constant) {
    my_constant = a_constant;
  }

  /**
   * Returns the link to the BCEL constant represented by the current line.
   * If there is no such constant it creates the constant before returning.
   * Newly created constant should then be associated with BML constant pool
   * representation. <br> <br>
   *
   * Implemented in subclasses.
   *
   * @return a BCEL constant represented by the current line
   */
  public Constant getConstant() {
    return my_constant;
  }

  /**
   * This method allows CPLineController subclasses to access my_constant.
   *
   * @return my_constant
   */
  public Constant getConstantAccessor() {
    return my_constant;
  }

  /**
   * This method changes all references to another CP entries
   * from a "dirty" numbers to a "clean" ones in BCEL representation
   * of this CP entry. <br> <br>
   *
   * See {@link BytecodeController#recalculateCPNumbers()} for explantation of
   * "dirty" and "clean" numbers concepts. <br> <br>
   *
   * Implemented in subclasses.
   *
   * @param a_map a hash map which maps "dirty" numbers to "clean" ones
   */
  public void updateReferences(final HashMap a_map) {

  }

  /**
   * This method checks if there are any references to non-existing
   * constant from this constant, and throws exception in such case.
   * <br> <br>
   * Implemented in subclasses.
   *
   * @param a_set a set of constant numbers in textual representation
   * of bytecode
   * @throws UmbraNoSuchConstantException if there is reference from
   * this constant to non-existing constant
   */
  public void checkCorrectness(final HashSet a_set)
    throws UmbraNoSuchConstantException {

  }

}
