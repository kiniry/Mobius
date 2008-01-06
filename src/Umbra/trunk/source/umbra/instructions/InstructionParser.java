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
 * This class allows to parse the line with instruction. It enables the
 * analysis of the correctness.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class InstructionParser {

  /**
   * Java reserved literals as enumerated in JLS 3rd edition, 3.9 Keywords.
   */
  private static final String[] JAVA_RES_LITERALS = {
    "null",  "true",  "false"
  };

  /**
   * Java reserved keywords as enumerated in JLS 3rd edition, 3.9 Keywords.
   */
  private static final String[] JAVA_KEYWORDS = {
    "abstract",  "continue",    "for",          "new",          "switch",
    "assert",    "default",     "if",           "package",      "synchronized",
    "boolean",   "do",          "goto",         "private",      "this",
    "break",     "double",      "implements",   "protected",    "throw",
    "byte",      "else",        "import",       "public",       "throws",
    "case",      "enum",        "instanceof",   "return",       "transient",
    "catch",     "extends",     "int",          "short",        "try",
    "char",      "final",       "interface",    "static",       "void",
    "class",     "finally",     "long",         "strictfp",     "volatile",
    "const",     "float",       "native",       "super",        "while"
  };

  /**
   * This field contains the value of the instruction line
   * which is parsed.
   */
  private String my_line;

  /**
   * The pointer inside the line. It points ot the first character which
   * has not been analysed yet. If this field is equal to my_line.length()
   * the analysis is finished.
   */
  private int my_index;
  //@ invariant 0 <= my_index && my_index <= my_line.length();

  /**
   * This field contains the number parsed from the chunk of the digits.
   * It contains a sensible value right after the {@ref #swallowNumber()}
   * is called.
   */
  private int my_result;

  /**
   * This constructor sets the string to be parsed and resets the parser
   * so that it is ready to analyse the content.
   *
   * @param a_line the line with the content to parse
   */
  public /*@ pure @*/ InstructionParser(final String a_line) {
    my_line = a_line;
    resetParser();
  }

  /*@
    @ ensures my_index == 0;
    @*/
  /**
   * This method resets the parser so that it starts the analysis
   * from the beginning.
   */
  public void resetParser() {
    my_index = 0;
  }

  /**
   * This method swallows all the whitespace starting from the current
   * position of the index. This method may not advance the index in case
   * the first character to be analysed is not whitespace.
   *
   * @return <code>true</code> when the further analysis is not finished yet,
   *   <code>false</code> when at the end of the string
   */
  public boolean swallowWhitespace() {
    if (my_index == my_line.length()) return false;
    while (Character.isWhitespace(my_line.charAt(my_index))) {
      my_index++;
      if (my_index == my_line.length()) return false;
    }
    return true;
  }

  /**
   * This method swallows all the digits starting from the current
   * position of the index. This method may not advance the index in case
   * the first character to be analysed is not a digit or the analysis is
   * finished before the method is called. This method assumes that a
   * number is finished when a whitespace or end of string is met.
   * In case the whitespace is not met after the string the number is not
   * considered to be successfully swallowed.
   *
   * @return <code>true</code> when a number was successfully swallowed,
   *   <code>false</code> otherwise
   */
  public boolean swallowNumber() {
    boolean res = true;
    if (my_index == my_line.length()) res = false;
    final int oldindex = my_index;
    while (Character.isDigit(my_line.charAt(my_index)) && res) {
      my_index++;
      if (my_index == my_line.length()) break;
    }
    if (oldindex == my_index) return false; //no digits were read
    if (my_index < my_line.length() &&
        !Character.isWhitespace(my_line.charAt(my_index)))
      // the line is not finished and the character at index is not whitespace
      return false;
    my_result = Integer.parseInt(my_line.substring(oldindex, my_index));
    return true;
  }

  /**
   * This method swallows the given delimiter. This method may not advance
   * the index in case the first character to be analysed is not the delimiter
   * or the analysis is finished before the method is called.
   *
   * @param a_ch the character with the delimiter to swallow
   * @return <code>true</code> when the delimiter was successfully swallowed,
   *   <code>false</code> otherwise
   */
  public boolean swallowDelimiter(final char a_ch) {
    if (my_index == my_line.length()) return false;
    if (my_line.charAt(my_index) == a_ch) {
      my_index++;
      return true;
    }
    return false;
  }

  /**
   * Checks if the line at the current position starts with a mnemonic from
   * the inventory.
   *
   * @param the_inventory the array of the mnemonics to be checked
   * @return the index to the entry in the inventory which contains the
   *   mnemonic or -1 in case no mnemonic from the inventory occurs
   */
  public int swallowMnemonic(final String[] the_inventory) {
    int res = -1;
    for (int i = 0; i < the_inventory.length; i++) {
      if (my_line.indexOf(the_inventory[i], my_index) == my_index) {
        if (res == -1 ||
            the_inventory[res].length() >  the_inventory[i].length())
          res = i;
      }
    }
    return res;
  }

  /**
   * @return the number which is the result of parsing
   */
  public int getResult() {
    return my_result;
  }

  /**
   * @return <code>true</code> when the index is at the end of the parsed
   *   string
   */
  public boolean isFinished() {
    return my_index == my_line.length();
  }

  /**
   * The method moves the current index right after the first occurrence of
   * the given delimiter character {@ref #a_ch}. In case the character does
   * not occur in the part of the parsed string starting at the current index,
   * then the index is set so that the parser is finished.
   *
   * @param a_ch the delimiter character which is sought
   */
  public void seekDelimiter(final char a_ch) {
    final int where = my_line.indexOf(a_ch, my_index);
    if (where > 0)
      my_index = my_line.length();
    else
      my_index = where + 1;
  }

  /**
   * The method moves the current index right after the first occurrence of
   * one of the mnemonics from <code>an_inventory</code>. We pick the
   * longest mnemonic that occurs in the string. In case none of the
   * mnemonics from <code>the_inventory</code> occurs in the part of the parsed
   * string starting at the current index, then the index is set so that the
   * parser is finished.
   *
   * @param the_inventory  the array of the mnemonics to be checked
   */
  public void seekMnemonic(final String[] the_inventory) {
    int res = -1;
    for (int i = 0; i < the_inventory.length; i++) {
      if (my_line.indexOf(the_inventory[i], my_index) >= my_index) {
        if (res == -1 ||
            the_inventory[res].length() >  the_inventory[i].length())
          res = i;
      }
    }
    my_index = my_line.indexOf(the_inventory[res], my_index) +
               the_inventory[res].length();
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
    while (swallowIdentifier()) {
      if (!(my_line.charAt(my_index) == '.')) {
        return Character.isWhitespace(my_line.charAt(my_index)) ||
            my_line.charAt(my_index) == '>';
      }
      my_index++;
    }
    return false;
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
   * {@ref Character#isJavaIdentifierStart(int)} returns true and
   * a "JavaLetterOrDigit" is a character for which the method
   * {@ref Character#isJavaIdentifierPart(int)} returns true.
   *
   * @return <code>true</code> when the identifier has been properly identified
   *   and swallowed, <code>false</code> when the starting portion of the
   *   string cannot start an identifier
   */
  private boolean swallowIdentifier() {
    if (!Character.isJavaIdentifierStart(my_line.charAt(my_index)))
      return false;
    final StringBuffer buf = new StringBuffer("");
    do {
      buf.append(my_line.charAt(my_index));
      my_index++;
    } while (Character.isJavaIdentifierPart(my_line.charAt(my_index)));
    final String s = new String(buf);
    return !isJavaResLiteral(s) && !isJavaKeyword(s);
  }

  /**
   * Checks if the given string is a Java keyword.
   *
   * @param a_string the string to check
   * @return <code>true</code> when the given string is a Java keyword,
   *   <code>false</code> otherwise
   */
  private boolean isJavaKeyword(final /*@ non_null @*/ String a_string) {
    for (int i = 0; i < JAVA_KEYWORDS.length; i++)
      if (a_string.equals(JAVA_KEYWORDS[i])) return true;
    return false;
  }

  /**
   * Checks if the given string is a Java reserved literal.
   *
   * @param a_string the string to check
   * @return <code>true</code> when the given string is a Java reserved literal
   *   <code>false</code> otherwise
   */
  private boolean isJavaResLiteral(final /*@ non_null @*/ String a_string) {
    for (int i = 0; i < JAVA_RES_LITERALS.length; i++)
      if (a_string.equals(JAVA_RES_LITERALS[i])) return true;
    return false;
  }
}
