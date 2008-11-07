/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import umbra.instructions.ClassHeaderParser;

/**
 * This is a class for lines in bytecode files that occur at the beginning
 * of classes. These are intended not to be edited by a user.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class ClassHeaderLineController extends BytecodeLineController {

  /**
   * This object contains a parser which allows to check the
   * correctness of the header code line and to parse its parameters.
   */
  private ClassHeaderParser my_headerparser;

  /**
   * This creates an instance of a bytecode line handle
   * which occurs at the beginning of a class. Currently it just calls the
   * constructor of the superclass.
   *
   * @param a_line_text the string representation of the line text
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public ClassHeaderLineController(final String a_line_text) {
    super(a_line_text);
  }

  /**
   * Checks the correctness of the current header line. This routine follows
   * the definition from the BML Reference Manual. The format of the line
   * follows the following grammar:
   *
   *  class ident [ class-extends-clause} ] [ implements-clause} ]
   *
   * @return <code>true</code> when the line complies with the header
   *   definition, <code>false</code> otherwise
   */
  public final boolean correct() {
    boolean res = true;
    final ClassHeaderParser parser = getHeaderParser();
    parser.resetParser();
    res = res && parser.swallowClass();
    res = res && parser.swallowWhitespace();
    if (res) {
      res = parseIdent(parser);
    }
    if (parser.swallowWhitespace())
      parser.swallowExtendsClause();
    if (res && parser.swallowWhitespace())
      parser.swallowImplementsClause();
    if (res && !parser.swallowWhitespace())
      return res;
    else
      return false;
  }

  /**
   * This method parses the class identifier. It tries to parse it so that
   * the segments are separated with '.' and in case of failure it tries
   * to parse it as if it was separated with '/'.
   *
   * @param a_parser the parser to parse the identifier
   * @return <code>true</code> in case the identifier was correctly parsed,
   *   <code>false</code> otherwise
   */
  private boolean parseIdent(final ClassHeaderParser a_parser) {
    boolean res = true;
    final int ind = a_parser.getIndex();
    res = res && a_parser.swallowClassnameWithDelim('.');
    if (!res) { //retry with '/'
      a_parser.moveIndex(a_parser.getIndex() - ind);
      res = res && a_parser.swallowClassnameWithDelim('/');
    }
    return res;
  }

  /**
   * Lazy getter for the parser of the class header lines.
   *
   * @return the parser to parse the header lines
   */
  private ClassHeaderParser getHeaderParser() {
    if (my_headerparser == null) {
      my_headerparser = new ClassHeaderParser(getLineContent());
    }
    return my_headerparser;
  }
}
