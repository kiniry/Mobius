/*
 * @title "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright "(c) 2007-2009 University of Warsaw"
 * @license "All rights reserved. This program and the accompanying materials
 * are made available under the terms of the LGPL licence see LICENCE.txt file"
 */
package umbra.instructions;

/**
 * This class allows to parse the line with instruction or constant pool
 * entry. It enables the analysis of the correctness.
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class InstructionParser extends InstructionTypeParser {

  /**
   * This field contains the number parsed from the chunk of the digits.
   * It contains a sensible value right after the {@link #swallowNumber()}
   * is called.
   */
  private int my_result;

  /**
   * This field contains the number parsed from the chunk of the digits.
   * It contains a sensible value right after the {@link #swallowLongNumber()}
   * is called.
   */
  private long my_long_result;

  /**
   * This field contains the string representation of parsed floating point
   * number. It contains a sensible value right after the
   * {@link #swallowFloatingPointNumber()} is called.
   */
  private String my_fp_result;

  /**
   * This constructor sets the string to be parsed and resets the parser
   * so that it is ready to analyse the content. It relies on the
   * work in the superclass.
   *
   * @param a_line the line with the content to parse
   */
  public/*@ pure @*/InstructionParser(final String a_line) {
    super(a_line);
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
    final String line = getLine();
    int index = getIndex();
    if (index == line.length())
      res = false;
    final int oldindex = index;
    while (Character.isDigit(line.charAt(index)) && res) {
      index = incIndex();
      if (index == line.length())
        break;
    }
    if (oldindex == index)
      return false; //no digits were read
    if (index < line.length() &&
      !Character.isWhitespace(line.charAt(index)) &&
      line.charAt(index) != ':' &&
        line.charAt(index) != ';' && line.charAt(index) != ')')
      // the line is not finished and the character at index is not whitespace
      // or : or ;
      return false;
    my_result = Integer.parseInt(line.substring(oldindex, index));
    return true;
  }

  /**
   * This method swallows all the digits starting from the current
   * position of the index and the 'l' or 'L' character (if any).
   * This method may not advance the index in case
   * the first character to be analysed is not a digit or the analysis is
   * finished before the method is called. This method assumes that a
   * number is finished when a whitespace or end of string is met.
   * In case the whitespace is not met after the string the number is not
   * considered to be successfully swallowed.
   *
   * @return <code>true</code> when a number was successfully swallowed,
   *   <code>false</code> otherwise
   */
  public boolean swallowLongNumber() {
    boolean res = true;
    final String line = getLine();
    int index = getIndex();
    if (index == line.length())
      res = false;
    final int oldindex = index;
    while (Character.isDigit(line.charAt(index)) && res) {
      index = incIndex();
      if (index == line.length())
        break;
    }
    if (index < line.length() && res &&
        (line.charAt(index) == 'L' || line.charAt(index) == 'l'))
      index = incIndex();
    if (oldindex == index)
      return false; //no digits were read
    if (index < line.length() && !Character.isWhitespace(line.charAt(index)) &&
        line.charAt(index) != ':' && line.charAt(index) != ';' &&
        line.charAt(index) != ')')
      // the line is not finished and the character at index is not whitespace
      // or : or ;
      return false;
    // TODO (to23611) check whether index - 1 > 0
    if (line.charAt(index - 1) == 'L' || line.charAt(index - 1) == 'l')
      my_long_result = Long.parseLong(line.substring(oldindex, index - 1));
    else
      my_long_result = Long.parseLong(line.substring(oldindex, index));
    return true;
  }

  /**
   * This method swallows all the digits starting from the current
   * position of the index. This method may not advance the index in case
   * the first character to be analysed is not a digit or the analysis is
   * finished before the method is called. This method assumes that a
   * number is finished when a whitespace, dot, colon, semicolon, equals
   * sign or end of string is met.
   * Otherwise the number is not considered to be successfully swallowed.
   * This method is assumed to be used in parsing of constant pool
   * references in constant pool entries. The number is not successfully
   * swallowed if it start with 0.
   *
   * @return <code>true</code> when a number was successfully swallowed,
   *   <code>false</code> otherwise
   */
  public boolean swallowCPReferenceNumber() {
    boolean res = true;
    final String line = getLine();
    int index = getIndex();
    if (index == line.length()) {
      res = false;
    }
    final int oldindex = index;
    if (res && Character.isDigit(line.charAt(index)) &&
        line.charAt(index) != '0')
      index = incIndex();
    if (index < line.length()) {
      while (Character.isDigit(line.charAt(index)) && res) {
        index = incIndex();
        if (index == line.length())
          break;
      }
    }
    if (oldindex == index) {
      return false; //no digits were read
    }
    if (index < line.length() && !Character.isWhitespace(line.charAt(index)) &&
        line.charAt(index) != ':' && line.charAt(index) != ';' &&
        line.charAt(index) != '.' && line.charAt(index) != '=')
      // the line is not finished and the character at index is not whitespace
      // or : or . or = or ;
      return false;
    my_result = Integer.parseInt(line.substring(oldindex, index));
    return true;
  }

  /**
   * This method swallows all the characters which are parts of a correct
   * floating point number. The parsing starts from the current position
   * of the index. This method assumes that a number is finished when
   * automaton {@link RegExpAutomaton} accepts it (see
   * Umbra/docs/codedocs/automaton.eps for automaton schema).
   * The automaton will stop processing number
   * when it read character for which its current state doesn't have an
   * outgoing edges ot if it will reach end of line. If that current state
   * is an accepting state the automaton accepts number.
   * The floating point number is considered correct if it complies to the
   * format described in "Textual Representation of Specifications" of
   * "BML Reference Manual".
   *
   * @return <code>true</code> when a number was successfully swallowed,
   *   <code>false</code> otherwise
   *
   */
  public boolean swallowFPNumber() {
    final int oldindex = getIndex();
    final RegExpAutomaton automaton = RegExpAutomaton.constructAutomaton();
    if (!automaton.exec(getLine(), getIndex()))
      return false;
    moveIndex(automaton.getIndex() - oldindex);
    my_fp_result = getLine().substring(oldindex, getIndex());
    return true;
  }

  /**
   * @return the number which is the result of parsing
   */
  public int getResult() {
    return my_result;
  }

  /**
   * @return the long number which is the result of parsing
   */
  public long getLongResult() {
    return my_long_result;
  }

  /**
   * @return the string representation of the floating
   * point number which is the result of parsing
   */
  public String getFPResult() {
    return my_fp_result;
  }

  /**
   * The method moves the current index right after the first occurrence of
   * the given delimiter character {@code a_ch}. In case the character does
   * not occur in the part of the parsed string starting at the current index,
   * then the index is set so that the parser is finished.
   *
   * @param a_ch the delimiter character which is sought
   */
  public void seekDelimiter(final char a_ch) {
    final String line = getLine();
    final int index = getIndex();
    final int where = line.indexOf(a_ch, index);
    int offset = 0;
    if (where < 0)
      offset = line.length() - index;
    else
      offset = where + 1;
    moveIndex(offset);
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
    final String line = getLine();
    final int index = getIndex();
    int res = -1;
    for (int i = 0; i < the_inventory.length; i++) {
      if (line.indexOf(the_inventory[i], index) >= index) {
        if (res == -1 ||
            the_inventory[res].length() > the_inventory[i].length())
          res = i;
      }
    }
    moveIndex(line.indexOf(the_inventory[res], index) +
              the_inventory[res].length() - index);
  }

  /**
   * This method swallows a single string. This method may not
   * advance the index in case the first character to be analysed is not the
   * proper first character of a string. We assume the parsed string is not
   * finished before the method is called. We assume there is no newline
   * character in the parsed string. The parser index is located at the
   * return either at the position of the final " (when <code>true</code> is
   * returned) or right after the end of the parsed string (when
   * <code>false</code> is returned.
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
    final String line = getLine();
    final int len = line.length();
    while (getIndex() < len && line.charAt(getIndex()) != '"') {
      if (line.charAt(getIndex()) == '\\') {
        if (!swallowEscape())
          return false;
      } else {
        incIndex();
      }
    }
    return getIndex() < len;
  }

  /**
   * This method swallows a single escape sequence. This method may not
   * advance the index in case the first character to be analysed is not the
   * proper first character of an escape sequence i.e. '\\'. We assume the
   * parsed string is not finished before the method is called. We assume there
   * is no newline character in {@link #getLine()} string.
   *
   * The precise format as described in JLS 3rd edition, 3.10.6 Escape Sequences
   * for Character and String Literals, is:
   * <pre>
   * EscapeSequence:
   *     \ b                     - \u0008: backspace BS
   *     \ t                     - \u0009: horizontal tab HT
   *     \ n                     -
  : linefeed LF
   *     \ f                     - \u000c: form feed FF
   *     \ r                     -
  : carriage return CR
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
    final String line = getLine();
    int index = getIndex();
    boolean res = true;
    if (line.charAt(index) == '\\') {
      index = incIndex();
    } else {
      return false;
    }
    if (InstructionParserHelper.isOctalDigit(line.charAt(index))) {
      return swallowOctalNumber();
    } else if (InstructionParserHelper.isEscapeChar(line.charAt(index))) {
      index = incIndex();
      res = true;
    } else {
      res = false;
    }
    return res;
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
    final String line = getLine();
    final int index = getIndex();
    boolean ztt = false;
    if (InstructionParserHelper.isZeroToThreeDigit(line.charAt(index))) {
      ztt = true;
    }
    for (int i = 0; i < InstructionParserHelper.MAX_OCTAL_NUMBER_LENGTH; i++) {
      if (!InstructionParserHelper.isOctalDigit(line.charAt(index))) {
        incIndex();
        return true;
      } else {
        incIndex();
        if (i == InstructionParserHelper.MAX_OCTAL_NUMBER_LENGTH - 1) {
          return ztt;
        }
      }
    }
    return false;
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
    if (!swallowMethodName())
      return false;
    if (!swallowWhitespace())
      return false;
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
    final String line = getLine();
    boolean res = true;
    res = res && swallowDelimiter('(');
    while (line.charAt(getIndex()) != ')' && res) {
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
    final String line = getLine();
    final int index = getIndex();
    boolean res = true;
    if (InstructionParserHelper.isBaseTypeDescriptor(line.charAt(index)) ||
        InstructionParserHelper.isVoidTypeDescriptor(line.charAt(index))) {
      incIndex();
      return true;
    }
    res = res && swallowRefTypeDescriptor();
    return res;
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
   * This method swallows a signed number starting from the current
   * position of the index. This method may not advance the index in case
   * the first character to be analysed is not a digit or "-".
   * This method assumes that a
   * number is finished when a whitespace or end of string is met.
   * In case the whitespace is not met after the string the number is not
   * considered to be successfully swallowed.
   *
   * @return <code>true</code> when a number was successfully swallowed,
   *   <code>false</code> otherwise
   */
  public boolean swallowSignedNumber() {
    boolean res = true;
    final String line = getLine();
    final int index = getIndex();
    if (index == line.length())
      res = false;
    if (line.charAt(index) == '-' && res) {
      incIndex();
      res = swallowNumber();
      my_result = -my_result;
    } else {
      res = swallowNumber();
    }
    return res;
  }

}
