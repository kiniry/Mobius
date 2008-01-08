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
   * The maximal length of an octal escape.
   */
  private static final int MAX_OCTAL_NUMBER_LENGTH = 3;

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
   * The number of the last parsed mnemonic. The number is an index in the
   * array given as the parameter to {@ref #swallowMnemonic(String[])}.
   * If no sensible mnemonic have been found the field has the value -1;
   */
  private int my_mnemonicno = -1;

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
    if (my_index == my_line.length() ||
        my_line.substring(my_index).startsWith(getEOL())) return false;
    while (Character.isWhitespace(my_line.charAt(my_index))) {
      my_index++;
      if (my_index == my_line.length() ||
          my_line.substring(my_index).startsWith(getEOL())) return false;
    }
    return true;
  }

  /**
   * @return the line separator specific for the current system
   */
  private String getEOL() {
    if (a_LINE_SEPARATOR == null)
      a_LINE_SEPARATOR = System.getProperty("line.separator");
    return a_LINE_SEPARATOR;
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
        !Character.isWhitespace(my_line.charAt(my_index)) &&
        my_line.charAt(my_index) != ':' &&
        my_line.charAt(my_index) != ')')
      // the line is not finished and the character at index is not whitespace
      // or :
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
    my_mnemonicno  = -1;
    for (int i = 0; i < the_inventory.length; i++) {
      if (my_line.indexOf(the_inventory[i], my_index) == my_index) {
        if (my_mnemonicno == -1 ||
            the_inventory[my_mnemonicno].length() >  the_inventory[i].length())
          my_mnemonicno = i;
      }
    }
    if (my_mnemonicno >= 0) {
      my_index += the_inventory[my_mnemonicno].length();
    }
    return my_mnemonicno;
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

  /**
   * This method swallows a single string. This method may not
   * advance the index in case the first character to be analysed is not the
   * proper first character of a string. We assume the parsed string is not
   * finished before the method is called. We assume there is no newline
   * character in {@ref #my_line}.
   *
   * The exact format, according to JLS 3rd edition 3.10.5 String Literals, is:
   * <pre>
   * StringLiteral:
   *         " StringCharacters_opt "
   *
   * StringCharacters:
   *         StringCharacter
   *         StringCharacters StringCharacter
   *
   * StringCharacter:
   *         InputCharacter but not " or \
   *         EscapeSequence
   * </pre>
   *
   * @return <code>true</code> when the string has been properly identified
   *   and swallowed, <code>false</code> when the starting portion of the
   *   string cannot start a string
   */
  public boolean swallowString() {
    while (my_line.charAt(my_index) != '"') {
      if (my_line.charAt(my_index) == '\\') {
        if (!swallowEscape()) return false;
      } else {
        my_index++;
      }
    }
    return true;
  }

  /**
   * This method swallows a single escape sequence. This method may not
   * advance the index in case the first character to be analysed is not the
   * proper first character of an escape sequence i.e. '\\'. We assume the
   * parsed string is not finished before the method is called. We assume there
   * is no newline character in {@ref #my_line}.
   *
   * The precise format as described in JLS 3rd edition, 3.10.6 Escape Sequences
   * for Character and String Literals, is:
   * <pre>
   * EscapeSequence:
   *     \ b                     - \u0008: backspace BS
   *     \ t                     - \u0009: horizontal tab HT
   *     \ n                     - \u000a: linefeed LF
   *     \ f                     - \u000c: form feed FF
   *     \ r                     - \u000d: carriage return CR
   *     \ "                     - \u0022: double quote "
   *     \ '                     - \u0027: single quote '
   *     \ \                     - \u005c: backslash \
   *     OctalEscape             - \u0000 to \u00ff: from octal value
   * </pre>
   *
   * @return <code>true</code> when the escape sequence has been properly
   *   identified and swallowed, <code>false</code> when the starting portion
   *   of the string cannot start a string
   */
  private boolean swallowEscape() {
    boolean res = true;
    if (my_line.charAt(my_index) == '\\') {
      my_index++;
    } else {
      return false;
    }
    if (isOctalDigit(my_line.charAt(my_index))) {
      return swallowOctalNumber();
    } else if (isEscapeChar(my_line.charAt(my_index))) {
      my_index++;
      res = true;
    } else {
      res = false;
    }
    return res;
  }

  /**
   * Check if a character is a meaningful escape character. The meaningful
   * escape characters are as described in JLS 3rd edition, 3.10.6 Escape
   * Sequences for Character and String Literals: b, t, n, f, r, ", ', \.
   *
   * @param a_char the character to check
   * @return <code>true</code> when a_char is a meaningful escape character
   */
  private boolean isEscapeChar(final char a_char) {
    for (int i = 0; i < ESCAPE_CODE_CHARACTERS.length(); i++)
      if (ESCAPE_CODE_CHARACTERS.charAt(i) == a_char) return true;
    return false;
  }

  /**
   * This method swallows an octal number form an octal escape sequence.
   * We assume the parsed string is not finished before the method is called.
   * The precise format as described in JLS 3rd edition, 3.10.6 Escape Sequences
   * for Character and String Literals, is:
   * <pre>
   * OctalEscape:
   *     \ OctalDigit
   *     \ OctalDigit OctalDigit
   *     \ ZeroToThree OctalDigit OctalDigit
   * </pre>
   * This method assumes that \ is already swallowed.
   *
   * @return <code>true</code> when an octal number has been successfully
   *   swallowed, <code>false</code> otherwise
   */
  private boolean swallowOctalNumber() {
    boolean ztt = false;
    if (isZeroToThreeDigit(my_line.charAt(my_index))) ztt = true;
    for (int i = 0; i < MAX_OCTAL_NUMBER_LENGTH; i++) {
      if (!isOctalDigit(my_line.charAt(my_index++))) {
        return true;
      } else {
        if (i == MAX_OCTAL_NUMBER_LENGTH - 1) return ztt;
      }
    }
    return false;
  }

  /**
   * Check if a character is an octal digit.
   *
   * @param a_char the character to check
   * @return <code>true</code> when a_char is an octal digit
   */
  private boolean isOctalDigit(final char a_char) {
    for (int i = 0; i < OCTAL_DIGITS.length(); i++)
      if (OCTAL_DIGITS.charAt(i) == a_char) return true;
    return false;
  }

  /**
   * Check if a character is 0, 1, 2, or 3.
   *
   * @param a_char the character to check
   * @return <code>true</code> when a_char is 0, 1, 2, or 3
   */
  private boolean isZeroToThreeDigit(final char a_char) {
    for (int i = 0; i < ZEROTOTHREE_DIGITS.length(); i++)
      if (ZEROTOTHREE_DIGITS.charAt(i) == a_char) return true;
    return false;
  }

  /**
   * Returns the index of the last mnemonic found by
   * {@ref #swallowMnemonic(String[])}. In case no mnemonic was found, the
   * method returns -1.
   *
   * @return the number of the last mnemonic found
   */
  public int getMnemonic() {
    return my_mnemonicno;
  }
  /**
   * This method swallows a single method reference. This method may not
   * advance the index in case the first character to be analysed is not the
   * proper first character of a reference name. We assume the string is not
   * finished before the method is called.
   *
   * As JVMS, 5.1 The Runtime Constant Pool says, a symbolic reference gives
   * the name and descriptor of the method, as well as a symbolic reference to
   * the class in which the method is to be found. This takes up the form:
   * <pre>
   *   (Identifier .)* Identifier whitespace MethodDescriptor
   * </pre>
   *
   * @return <code>true</code> when a method symbolic reference is successfully
   *   swallowed, <code>false</code> otherwise
   */
  public boolean swallowMethodReference() {
    if (!swallowMethodName()) return false;
    if (!swallowWhitespace()) return false;
    return swallowMethodDescriptor();
  }

  /**
   * This method swallows a single method descriptor. This method may not
   * advance the index in case the first character to be analysed is not the
   * proper first character of a reference name. We assume the string is not
   * finished before the method is called.
   *
   * As JVMS, 4.3.3 Method Descriptors says, a method descriptor represents the
   * parameters that the method takes and the value that it returns:
   * <pre>
   * MethodDescriptor:
   *      ( ParameterDescriptor* ) ReturnDescriptor
   * </pre>
   *
   * @return <code>true</code> when a method descriptor is successfully
   *   swallowed, <code>false</code> otherwise
   */
  private boolean swallowMethodDescriptor() {
    boolean res = true;
    res = res && swallowDelimiter('(');
    if (my_line.charAt(my_index) != ')') {
      res = res && swallowParameterDescriptor();
    }
    res = res && swallowDelimiter(')');
    res = res && swallowWhitespace();
    return res && swallowReturnDescriptor();
  }

  /**
   * This method swallows a single return descriptor. This method may not
   * advance the index in case the first character to be analysed is not the
   * proper first character of a return descriptor. We assume the string is not
   * finished before the method is called.
   *
   * As JVMS, 4.3.3 Method Descriptors says, a return descriptor represents the
   * type of the value returned from a method. It is a series of characters
   * generated by the grammar:
   * <pre>
   * ReturnDescriptor:
   *     FieldType
   *     V
   * </pre>
   *
   * @return <code>true</code> when a return descriptor is successfully
   *   swallowed, <code>false</code> otherwise
   */
  private boolean swallowReturnDescriptor() {
    boolean res = false;
    if (isBaseTypeDescriptor(my_line.charAt(my_index)) ||
        isVoidTypeDescriptor(my_line.charAt(my_index))) {
      my_index++;
      res = true;
    }
    res = res && swallowRefTypeDescriptor();
    return res;
  }

  /**
   * This method swallows a reference type descriptor. This method may not
   * advance the index in case the first character to be analysed is not the
   * proper first character of an array descriptor. We assume the string is not
   * finished before the method is called.
   *
   * As JVMS, 4.3.3 Method Descriptors says, a filed type descriptor is
   * a series of characters generated by the grammar:
   * <pre>
   * FiledType:
   *   BaseType
   *   ArrayType
   *   ObjectType
   * </pre>
   * We omit here the BaseType case.
   *
   * @return <code>true</code> when a parameter descriptor is successfully
   *   swallowed, <code>false</code> otherwise
   */
  private boolean swallowRefTypeDescriptor() {
    boolean res = true;
    if (isArrayTypeDescriptor(my_line.charAt(my_index))) {
      my_index++;
      res = swallowArrayTypeDescriptor();
    }
    if (!res && isObjectTypeDescriptor(my_line.charAt(my_index))) {
      my_index++;
      res = swallowObjectTypeDescriptor();
    }
    return res;
  }

  /**
   * This method swallows an object type descriptor. This method may not
   * advance the index in case the first character to be analysed is not the
   * proper first character of an object type descriptor. We assume the string
   * is not finished before the method is called.
   *
   * As JVMS, 4.3.3 Method Descriptors says, an object type descriptor is
   * a series of characters generated by the grammar:
   * <pre>
   * ObjectType:
   *   L &lt;classname&gt; ;
   * </pre>
   * we assume L is already swallowed so we swallow here only the class name.
   *
   * @return <code>true</code> when a return descriptor is successfully
   *   swallowed, <code>false</code> otherwise
   */
  private boolean swallowObjectTypeDescriptor() {
    final boolean res = swallowClassnameWithDelim('/');
    return res && swallowDelimiter(';');
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
  private boolean swallowClassnameWithDelim(final char a_separator) {
    while (swallowIdentifier()) {
      if (!(my_line.charAt(my_index) == a_separator)) {
        return Character.isWhitespace(my_line.charAt(my_index)) ||
            my_line.charAt(my_index) == '>' ||
            my_line.charAt(my_index) == ';';
      }
      my_index++;
    }
    return false;
  }

  /**
   * Checks if the given character starts an object type descriptor.
   *
   * @param a_c a character to check
   * @return <code>true</code> when the character starts an object type
   *   descriptor
   */
  private boolean isObjectTypeDescriptor(final char a_c) {
    return (a_c == 'L');
  }

  /**
   * This method swallows an array type descriptor. This method may not
   * advance the index in case the first character to be analysed is not the
   * proper first character of an array descriptor. We assume the string is not
   * finished before the method is called.
   *
   * As JVMS, 4.3.3 Method Descriptors says, an object type descriptor is
   * a series of characters generated by the grammar:
   * <pre>
   * ArrayType:
   *   [ ComponentType ;
   * </pre>
   * we assume [ is already swallowed so we swallow here only the component
   * type.
   *
   * @return <code>true</code> when a return descriptor is successfully
   *   swallowed, <code>false</code> otherwise
   */
  private boolean swallowArrayTypeDescriptor() {
    boolean res = false;
    res = swallowFieldType(); //ComponentType :: = FieldType
    res = res && swallowDelimiter(';');
    return res;
  }

  /**
   * This method swallows a filed type descriptor. This method may not
   * advance the index in case the first character to be analysed is not the
   * proper first character of an array descriptor. We assume the string is not
   * finished before the method is called.
   *
   * As JVMS, 4.3.3 Method Descriptors says, a filed type descriptor is
   * a series of characters generated by the grammar:
   * <pre>
   * FiledType:
   *   BaseType
   *   ArrayType
   *   ObjectType
   * </pre>
   *
   * @return <code>true</code> when a return descriptor is successfully
   *   swallowed, <code>false</code> otherwise
   */
  private boolean swallowFieldType() {
    boolean res = false;
    if (isBaseTypeDescriptor(my_line.charAt(my_index))) {
      my_index++;
      res = true;
    }
    res = res && swallowRefTypeDescriptor();
    return res;
  }

  /**
   * Checks if the given character starts an array type descriptor.
   *
   * @param a_c a character to check
   * @return <code>true</code> when the character starts an array type
   *   descriptor
   */
  private boolean isArrayTypeDescriptor(final char a_c) {
    return (a_c == '[');
  }

  /**
   * Checks if the given character starts a base type descriptor.
   *
   * @param a_c a character to check
   * @return <code>true</code> when the character starts a byse type
   *   descriptor
   */
  private boolean isBaseTypeDescriptor(final char a_c) {
    for (int i = 0; i < BASE_TYPE_DESCRIPTORS.length(); i++) {
      if (a_c == BASE_TYPE_DESCRIPTORS.charAt(i)) return true;
    }
    return false;
  }

  /**
   * Checks if the given character starts a void type descriptor.
   *
   * @param a_c a character to check
   * @return <code>true</code> when the character starts a void type
   *   descriptor
   */
  private boolean isVoidTypeDescriptor(final char a_c) {
    return (a_c == 'V');
  }

  /**
   * This method swallows a single parameter descriptor. This method may not
   * advance the index in case the first character to be analysed is not the
   * proper first character of a parameter descriptor. We assume the string is
   * not finished before the method is called.
   *
   * As JVMS, 4.3.3 Method Descriptors says, a parameter descriptor represents
   * a parameter passed to a method:
   * <pre>
   * ParameterDescriptor:
   *      FieldType
   * </pre>
   *
   * @return <code>true</code> when a parameter descriptor is successfully
   *   swallowed, <code>false</code> otherwise
   */
  private boolean swallowParameterDescriptor() {
    return swallowFieldType();
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
   * @return <code>true</code> when the method name has been suceessfully
   *   swallowed, <code>false</code> otherwise.
   */
  private boolean swallowMethodName() {
    while (swallowIdentifier()) {
      if (!(my_line.charAt(my_index) == '.')) {
        return Character.isWhitespace(my_line.charAt(my_index));
      }
      my_index++;
    }
    if (my_line.charAt(my_index) == '<') {
      swallowDelimiter('<'); //FIXME this is a hack to parse <init>
      swallowIdentifier();
      return swallowDelimiter('>');
    }
    return false;
  }
}
