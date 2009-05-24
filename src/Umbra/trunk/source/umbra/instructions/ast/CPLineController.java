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

import umbra.instructions.InstructionParser;
import umbra.lib.BytecodeStrings;
import umbra.lib.UmbraNoSuchConstantException;

import org.apache.bcel.classfile.Constant;


/**
 * This is a class for lines in bytecode files inside the constant pool.
 * <br> <br>
 *
 * TODO (to236111) should be made abstract after removing old implementation
 * ({@link umbra.instructions.Preparsing#getTypeForInsides(String,
 * LineContext, BMLParsing)})
 * <br> <Br>
 *
 * TODO (to236111) add parameter fields to avoid mulitple parsings of the
 * same line?
 *
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class CPLineController extends BytecodeLineController {

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
   * The parser to parse the contents of the constant pool line.
   * NOTE (to236111) already exists in superclass
   */
  // private InstructionParser my_parser;

  /**
   * The number of the constant in the constant pool which is represented
   * by the current line.
   */
  private int my_constno;

  /**
   * The keyword which identifies the type of the current constant pool
   * constant.
   * NOTE (to236111) reimplemented using subclasses
   */
  // private int my_keyword;

  /**
   * Link to the BCEL constant represented by this line.
   */
  private Constant my_constant;

  /**
   * This variable has value <code>true</code> if the constant pool entry
   * this line represents is present in BML representation of constant pool.
   */
  private boolean my_in_bml;

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
    my_in_bml = false;
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
    return a_line.startsWith(BytecodeStrings.CP_ENTRY_PREFIX[0]);
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
   * This method parses the content of the constant pool entry. Currently,
   * it only checks the correctness of the constant pool entry kind.
   *
   * @param an_utonow the status of the parsing up to the current position
   * @return <code>true</code> in case the method isCPLineStartwas called with
   *   <code>true</code> and the parsing of the content of the constant pool
   *   entry, <code>false</code> otherwise
   *
   *   NOTE (to236111) reimplemented in subclasses
   *
   */
  /* private boolean parseEntry(final boolean an_utonow) {
    if (!an_utonow) {
      return an_utonow;
    }
    boolean res = an_utonow;
    res = res && my_parser.swallowWhitespace();
    my_keyword = my_parser.swallowMnemonic(BytecodeStrings.CP_TYPE_KEYWORDS);
    res = res && (my_keyword >= 0);
    return res;
  } */

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
   * Returns <code>true</code> if the constant pool entry this line represents
   * is present in BML representation of constant pool, <code>false</code>
   * otherwise.
   *
   * @return <code>true</code> if the constant pool entry this line represents
   * is present in BML representation of constant pool
   */
  public boolean isInBML() {
    return my_in_bml;
  }

  /**
   * Sets whether the constant pool entry this line represents
   * is present in BML representation of constant pool.
   *
   * @param a_b value to set
   */
  public void setInBML(final boolean a_b) {
    my_in_bml = a_b;
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
   * TODO (to236111) IMPORTANT check whether rollback of changes to BML
   * representation of constant needed in case of UmbraCPRecalculationException
   *
   * @param a_map a hash map which maps "dirty" numbers to "clean" ones
   * @throws UmbraNoSuchConstantException when "dirty" number refers to non
   * existing constant
   */
  public void updateReferences(final HashMap a_map)
    throws UmbraNoSuchConstantException {

  }

}
