/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import java.util.Enumeration;
import java.util.Hashtable;

import umbra.instructions.ast.InstructionLineController;

/**
 * This class contains the functionality of the {@link BytecodeController}
 * class which is responsible for the handling of the end-of-line comments
 * and interline comments.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public abstract class BytecodeControllerComments
  extends BytecodeControllerHelper {


  /**
   * The container of all the multi-line comments. Each element of the table is
   * an association between an instruction line and a string with comments.
   * The string may contain several lines of text. For a given instruction,
   * the string contains the comment that is located after it.
   * FIXME: this functionality is not realised in the current version.
   *        https://mobius.ucd.ie/ticket/555
   * @see #getInterlineComments()
   */
  private Hashtable my_interline;

  /**
   * The container of associations between the Umbra representation of lines
   * in the byte code editor and the end-of-line comments in these lines.
   * The comments must be absent from the line representation for their
   * correct parsing so they are held in this additional structure.
   *
   * @see #getEOLComments()
   */
  private Hashtable my_eolcomments;

  /**
   * The constructor does only the initialisation of the superclass. The
   * fields of this class are left intact for later initialisation.
   */
  public BytecodeControllerComments() {
    super();
  }

  /**
   * This method updates the local representation of end-of-line comments
   * within the given range with the given new comment content.
   * The range of the old lines from {@code the_first} to {@code the_oldlast}
   * is removed from the current representation and in that range the
   * information for the lines from {@code the_first} to {@code the_newlast}
   * is inserted as indicated in the {@code comments} parameter.
   *
   * @param the_first the first line of the edited region
   * @param the_oldlast the last line of the old document
   * @param the_newlast the last line of the new document
   * @param the_comments te comments to add to the internal representation
   */
  protected void updateComments(final int the_first,
                              final int the_oldlast,
                              final int the_newlast,
                              final Hashtable the_comments) {
    for (int i = the_first; i <= the_oldlast; i++) {
      final Object o = getLineController(i);
      my_eolcomments.remove(o);
    }
    for (final Enumeration enumer = the_comments.keys();
         enumer.hasMoreElements();) {
      final Object key = enumer.nextElement();
      final Object value = the_comments.get(key);
      my_eolcomments.put(key, value);
    }
  }


  /**
   * This method returns the interoperable representation of the end-of-line
   * comments. The i-th entry in the returned array gives the end-of-line
   * comment that is located <i>after</i> the i-th instruction in the file.
   * Each entry contains at most one line of text.
   *
   * @return array with end-of-line comments
   */
  public String[] getEOLComments() {
    final String[] commentTab = new String[getNoOfInstructions()];
    for (int i = 0; i < getNoOfInstructions(); i++) {
      final InstructionLineController lc = getInstruction(i);
      final String com = (String)my_eolcomments.get(lc);
      commentTab[i] = com;
    }
    return commentTab;
  }

  /**
   * This method returns the interoperable representation of the multi-line
   * comments. The i-th entry in the returned array gives the multi-line comment
   * that is located <i>after</i> the i-th instruction in the file. Each entry
   * may contain several lines of text.
   *
   * @return array with multi-line comment strings
   */
  public String[] getInterlineComments() {
    final String[] commentTab = new String[getNoOfInstructions()];
    for (int i = 0; i < getNoOfInstructions(); i++) {
      final InstructionLineController lc = getInstruction(i);
      final String com = (String)my_interline.get(lc);
      commentTab[i] = com;
    }
    return commentTab;
  }

  /**
   * This method initialises the internal comments representation using
   * the given initial parser.
   *
   * @param the_parser the parser with the initial information on the comments
   * @param a_comment_array the array with the interoperable representation
   *   of end-of-line comments from the previous session
   * @param a_interline the array with the interoperable representation
   *   of interline comments from the previous session
   */
  protected void initComments(final InitParser the_parser,
                              final String[] a_comment_array,
                              final String[] a_interline) {
    my_eolcomments = the_parser.getComments();
    my_interline = the_parser.getInterlineComments();
  }

  /**
   * Returns the line controller for the given instruction number.
   * The instruction number is the sequence number of the instruction in
   * the textual file.
   *
   * @param an_insno the number of the retrieved instruction
   * @return the controller line for the given instruction number
   */
  protected abstract InstructionLineController getInstruction(
                                                  final int an_insno);

  /**
   * Returns the total number of the instructions in the current document.
   *
   * @return the number of instructions in the current document
   */
  protected abstract int getNoOfInstructions();
}
