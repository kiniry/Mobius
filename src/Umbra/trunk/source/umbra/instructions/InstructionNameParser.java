/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2007-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;


/**
 * This class is the part of the byte code instruction parser which contributes
 * the parsing of various identifiers i.e. field names, class names, and method
 * names.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class InstructionNameParser extends InstructionParserGeneric {

  /**
   * This constructor sets the string to be parsed and resets the parser
   * so that it is ready to analyse the content. It relies on the
   * work in the superclass. It can be called only from subclasses.
   *
   * @param a_line the line with the content to parse
   */
  protected InstructionNameParser(final String a_line) {
    super(a_line);
  }
  /**
   * This method swallows a single class name with different possible
   * name chunk separators. The separator is in the parameter
   * <code>a_separator</code>. This method may not advance the index in case
   * the first character to be analysed is not the proper first character of a
   * class name. We assume the string is not finished before the method is
   * called.
   *
   * The Java class name (TypeName) is parsed using the following specification:
   * <pre>
   * TypeName:
   *    Identifier
   *    TypeName separator Identifier
   * </pre>
   * from JLS 3rd edition, 4.3 Reference Types and Values. We additionally
   * assume that a Java classname is finished when it is followed either
   * by whitespace or by one of '>', ';'.
   *
   * @param a_separator the name chunk separator
   * @return <code>true</code> when the class name has been suceessfully
   *   swallowed, <code>false</code> otherwise.
   */
  public boolean swallowClassnameWithDelim(final char a_separator) {
    final String line = getLine();
    while (swallowIdentifier()) {
      if (getIndex() < line.length() &&
          line.charAt(getIndex()) != a_separator) {
        final int index = getIndex();
        return Character.isWhitespace(line.charAt(index)) ||
            line.charAt(index) == '>' ||
            line.charAt(index) == ';' ||
            line.charAt(index) == ',';
      } else if (getIndex() >= line.length()) {
        return true;
      }
      incIndex();
    }
    return false;
  }
  /**
   * This method swallows a single class name. This method may not
   * advance the index in case the first character to be analysed is not the
   * proper first character of a class name. We assume the string is not
   * finished before the method is called.
   *
   * The Java class name (TypeName) is parsed using the following specification:
   * <pre>
   * TypeName:
   *    Identifier
   *    TypeName . Identifier
   * </pre>
   * from JLS 3rd edition, 4.3 Reference Types and Values. We additionally
   * assume that a Java classname is finished when it is followed either
   * by whitespace or by '>'.
   *
   * @return <code>true</code> when the class name has been suceessfully
   *   swallowed, <code>false</code> otherwise.
   */
  public boolean swallowClassname() {
    return swallowClassnameWithDelim('.');
  }

  /**
   * This method swallows a single proper identifier. This method may not
   * advance the index in case the first character to be analysed is not the
   * proper first character of an identifier. We assume the string is not
   * finished before the method is called.
   *
   * The exact format, according to JLS 3rd edition 3.8 Identifiers, is:
   * <pre>
   * Identifier:
   *    IdentifierChars but not a Keyword or BooleanLiteral or NullLiteral
   *
   * IdentifierChars:
   *     JavaLetter
   *     IdentifierChars JavaLetterOrDigit
   * </pre>
   * where a "JavaLetter" is a character for which the method
   * {@link Character#isJavaIdentifierStart(int)} returns true and
   * a "JavaLetterOrDigit" is a character for which the method
   * {@link Character#isJavaIdentifierPart(int)} returns true.
   *
   * @return <code>true</code> when the identifier has been properly identified
   *   and swallowed, <code>false</code> when the starting portion of the
   *   string cannot start an identifier
   */
  public boolean swallowIdentifier() {
    final String line = getLine();
    int index = getIndex();
    if (!Character.isJavaIdentifierStart(line.charAt(index)))
      return false;
    final StringBuffer buf = new StringBuffer("");
    do {
      buf.append(line.charAt(index));
      index = incIndex();
    } while (index < line.length() &&
             Character.isJavaIdentifierPart(line.charAt(index)));
    final String s = new String(buf);
    return !InstructionParserHelper.isJavaResLiteral(s) &&
           !InstructionParserHelper.isJavaKeyword(s);
  }

  /**
   * This method swallows a single field name with different possible
   * name chunk separators. The separator is in the parameter
   * <code>a_separator</code>. This method may not advance the index in case
   * the first character to be analysed is not the proper first character of a
   * class name. We assume the string is not finished before the method is
   * called.
   *
   * We assume that a Java field name (TypeName) is parsed using the
   * following specification:
   * <pre>
   * FieldName:
   *    Identifier
   *    FieldName . Identifier
   * </pre>
   *
   * FIXME: this is not based on a part of JLS as I do not know where to find
   *        that; https://mobius.ucd.ie/ticket/553
   *
   * @return <code>true</code> when the class name has been successfully
   *   swallowed, <code>false</code> otherwise.
   */
  public boolean swallowFieldName() {
    final String line = getLine();
    while (swallowIdentifier()) {
      if (!(line.charAt(getIndex()) == '.')) {
        return Character.isWhitespace(line.charAt(getIndex())) ||
               line.charAt(getIndex()) == ';';
      }
      incIndex();
    }
    return false;
  }

  /**
   * This method swallows a single method name. This method may not
   * advance the index in case the first character to be analysed is not the
   * proper first character of a class name. We assume the string is not
   * finished before the method is called.
   *
   * The Java method name is parsed using the following specification:
   * <pre>
   * MethodName:
   *    Identifier
   *    MethodName . Identifier
   * </pre>
   * We additionally assume that a Java method is finished when it is followed
   * by whitespace.
   *
   * @return <code>true</code> when the method name has been successfully
   *   swallowed, <code>false</code> otherwise.
   */
  protected boolean swallowMethodName() {
    final String line = getLine();
    while (swallowIdentifier()) {
      if (!((line.charAt(getIndex()) == '.') ||
            (line.charAt(getIndex()) == '/'))) {
        return Character.isWhitespace(line.charAt(getIndex()));
      }
      incIndex();
    }
    if (line.charAt(getIndex()) == '<') {
      swallowDelimiter('<');
        //FIXME this is a hack to parse <init>; https://mobius.ucd.ie/ticket/554
      swallowIdentifier();
      return swallowDelimiter('>');
    }
    return false;
  }

  /**
   * This method swallows the particular given string from the parsed
   * text.
   *
   * @param a_word the word to swallow
   * @return <code>true</code> in case the word was successfully swallowed,
   *   <code>false</code> otherwise
   */
  public boolean swallowGivenWord(final String a_word) {
    if (getLine().regionMatches(getIndex(), a_word, 0, a_word.length())) {
      moveIndex(a_word.length());
      return true;
    }
    return false;
  }

}
