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
 * This class conatins helper methods that allow check the classes of
 * various syntactical classes occurring in Java byte code files.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public final class InstructionParserHelper {

  /**
   * The maximal length of an octal escape.
   */
  public static final int MAX_OCTAL_NUMBER_LENGTH = 3;

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
   * Octal digits.
   */
  private static final String OCTAL_DIGITS = "01234567";

  /**
   * Zero-three digits.
   */
  private static final String ZEROTOTHREE_DIGITS = "0123";

  /**
   * Base type descriptor characters.
   */
  private static final String BASE_TYPE_DESCRIPTORS = "BCDFIJSZ";

  /**
   * The meaningful escape characters. These are as described in JLS 3rd
   * edition, 3.10.6 Escape Sequences for Character and String Literals:
   * b, t, n, f, r, ", ', \.
   */
  private static final String ESCAPE_CODE_CHARACTERS = "btnfr\"\'\\";

  /**
   * Contains cached line separator string.
   */
  private static String a_LINE_SEPARATOR;

  /**
   * Empty private constructor to forbid the creation of objects with this
   * type.
   */
  private InstructionParserHelper() {
  }

  /**
   * @return the line separator specific for the current system
   */
  public static String getEOL() {
    if (a_LINE_SEPARATOR == null)
      a_LINE_SEPARATOR = System.getProperty("line.separator");
    return a_LINE_SEPARATOR;
  }

  /**
   * Checks if the given character starts an array type descriptor.
   *
   * @param a_c a character to check
   * @return <code>true</code> when the character starts an array type
   *   descriptor
   */
  public static boolean isArrayTypeDescriptor(final char a_c) {
    return (a_c == '[');
  }

  /**
   * Checks if the given character starts a base type descriptor.
   *
   * @param a_c a character to check
   * @return <code>true</code> when the character starts a byse type
   *   descriptor
   */
  public static boolean isBaseTypeDescriptor(final char a_c) {
    for (int i = 0; i < BASE_TYPE_DESCRIPTORS.length(); i++) {
      if (a_c == BASE_TYPE_DESCRIPTORS.charAt(i)) return true;
    }
    return false;
  }

  /**
   * Check if a character is a meaningful escape character. The meaningful
   * escape characters are as described in JLS 3rd edition, 3.10.6 Escape
   * Sequences for Character and String Literals: b, t, n, f, r, ", ', \.
   *
   * @param a_char the character to check
   * @return <code>true</code> when a_char is a meaningful escape character
   */
  public static boolean isEscapeChar(final char a_char) {
    for (int i = 0; i < ESCAPE_CODE_CHARACTERS.length(); i++)
      if (ESCAPE_CODE_CHARACTERS.charAt(i) == a_char) return true;
    return false;
  }

  /**
   * Checks if the given string is a Java keyword.
   *
   * @param a_string the string to check
   * @return <code>true</code> when the given string is a Java keyword,
   *   <code>false</code> otherwise
   */
  public static boolean isJavaKeyword(final /*@ non_null @*/ String a_string) {
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
  public static boolean isJavaResLiteral(
                             final /*@ non_null @*/ String a_string) {
    for (int i = 0; i < JAVA_RES_LITERALS.length; i++)
      if (a_string.equals(JAVA_RES_LITERALS[i])) return true;
    return false;
  }

  /**
   * Checks if the given character starts an object type descriptor.
   *
   * @param a_c a character to check
   * @return <code>true</code> when the character starts an object type
   *   descriptor
   */
  public static boolean isObjectTypeDescriptor(final char a_c) {
    return (a_c == 'L');
  }

  /**
   * Check if a character is an octal digit.
   *
   * @param a_char the character to check
   * @return <code>true</code> when a_char is an octal digit
   */
  public static boolean isOctalDigit(final char a_char) {
    for (int i = 0; i < OCTAL_DIGITS.length(); i++)
      if (OCTAL_DIGITS.charAt(i) == a_char) return true;
    return false;
  }

  /**
   * Checks if the given character starts a void type descriptor.
   *
   * @param a_c a character to check
   * @return <code>true</code> when the character starts a void type
   *   descriptor
   */
  public static boolean isVoidTypeDescriptor(final char a_c) {
    return (a_c == 'V');
  }

  /**
   * Check if a character is 0, 1, 2, or 3.
   *
   * @param a_char the character to check
   * @return <code>true</code> when a_char is 0, 1, 2, or 3
   */
  public static boolean isZeroToThreeDigit(final char a_char) {
    for (int i = 0; i < ZEROTOTHREE_DIGITS.length(); i++)
      if (ZEROTOTHREE_DIGITS.charAt(i) == a_char) return true;
    return false;
  }
}
