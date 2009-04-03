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
   * This creates an instance of a bytecode line handle to handle
   * constant pool entry.
   *
   * @param a_line_text the string representation of the line text
   * @param an_entry_type the entry type handled by the current class",
   * ignored parameter for compatibility with
   * {@link umbra.instructions.DispatchingAutomaton#callConstructor}
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public CPLineController(final String a_line_text, final String an_entry_type) {
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
}
