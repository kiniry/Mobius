/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.parsing;

import org.eclipse.jface.text.rules.IWhitespaceDetector;

/**
 * This class defines objects that are able to chceck if a particular character
 * is a whitespace.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeWhitespaceDetector implements IWhitespaceDetector {

  /**
   * The array which contains all the characters we consider here to be
   * whitespace characters.
   */
  public static final char[] WHITESPACE_CHARACTERS = {' ', '\t', '\n', '\r' };

  /**
   * This method defines which characters are whitespace characters.
   *
   * @param a_char the character to determine if it is whitespace
   * @return <code>true</code> when the character is regarded as a whitespace
   */
  public final boolean isWhitespace(final char a_char) {
    for (int i = 0; i < WHITESPACE_CHARACTERS.length; i++) {
      if (WHITESPACE_CHARACTERS[i] == a_char) return true;
    }
    return false;
  }
}
