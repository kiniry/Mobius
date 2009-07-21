/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.lib;

import org.eclipse.jface.text.rules.ICharacterScanner;

/**
 * The scanner to scan characters from buffers.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class BufferScanner implements ICharacterScanner {


  /**
   * The string buffer from which we scan the characters.
   */
  private String my_string;

  /**
   * The current position in the buffer. It ranges from 0 to
   * my_string.length (incl.)
   */
  private int my_pos;

  /**
   * Initialises the class with the given string buffer.
   *
   * @param a_buf the string to initialise the class with
   */
  public BufferScanner(final String a_buf) {
    my_string = a_buf;
    my_pos = 0;
  }

  /**
   * @return the column of the scanner (which is the position in the buffer)
   * @see org.eclipse.jface.text.rules.ICharacterScanner#getColumn()
   */
  public int getColumn() {
    return my_pos;
  }

  /**
   * @return <code>null</code> as the line delimiters table
   * @see org.eclipse.jface.text.rules.
   *   ICharacterScanner#getLegalLineDelimiters()
   */
  public char[][] getLegalLineDelimiters() {
    return null;
  }

  /**
   * @return the character at the current position in the buffer
   * @see org.eclipse.jface.text.rules.ICharacterScanner#read()
   */
  public int read() {
    if (0 <= my_pos && my_pos < my_string.length()) {
      return my_string.charAt(my_pos++);
    } else {
      return EOF;
    }
  }

  /**
   * Unreads one character from the scanner by decreasing the position in the
   * current buffer.
   */
  public void unread() {
    if (my_pos > 0) my_pos--;
  }

}
