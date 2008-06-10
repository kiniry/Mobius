/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.lib;

import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;

/**
 * This is just container for texts of all the GUI messages.
 *
 * FIXME: this does not contain all the messages
 *   https://mobius.ucd.ie/ticket/591
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public final class GUIMessages {

  /**
   * A string to indicate a point in a string template where the
   * data to instantiate the template should be substituted.
   */
  public static final String SUBSTITUTE = "#1#";


  /**
   * A string to indicate a point in a string template where the
   * second portion of data to instantiate the template should be substituted.
   */
  public static final String SUBSTITUTE2 = "#2#";

  /* *********************************************************************
   * GUI MESSAGES
   */

  /**
   * A string used as a generic header in the message panes launched in
   * connection with the byte code text editor.
   */
  public static final String BYTECODE_MESSAGE_TITLE = "Bytecode";

  /**
   * A string used as a header in the message panes launched in connection
   * with the Java source code action to disassemble code (class
   * {@link umbra.java.actions.DisasBCEL}).
   */
  public static final String DISAS_MESSAGE_TITLE =
    "Disassemble Bytecode";

  /**
   * A string used as a header in the message panes launched in connection
   * with the actions to synchronise the code (classes
   * {@link umbra.java.actions.SynchrSBAction} and
   * {@link umbra.editor.actions.BytecodeSynchrAction}).
   */
  public static final String SYNCH_MESSAGE_TITLE =
    "Synchronisation";

  /**
   * A string used as a header in the message panes launched in connection
   * with the Java source code action to commit changes (class
   * {@link umbra.java.actions.CommitAction}.
   */
  public static final String COMMIT_MESSAGE_TITLE =
    "Commiting changes";

  /**
   * The message which informs the user that the operation he/she wants to
   * carry out cannot be performed.
   */
  public static final String INVALID_EDIT_OPERATION = "Invalid edit operation";

  /**
   * The message which requires the user to save the byte code before it
   * is disassembled.
   */
  public static final String DISAS_SAVE_BYTECODE_FIRST =
    "You must save the source code before you can show its byte code.";

  /**
   * The message which informs the user that the file cannot be saved under
   * the given location.
   */
  public static final String DISAS_SAVING_PROBLEMS =
    "Problems with saving the file under the given location";

  /**
   * The message which informs the user that the file cannot be saved under
   * the given location.
   */
  public static final String DISAS_LOADING_PROBLEMS =
    "Problems with loading the file under the given location: ";

  /**
   * The message which informs the user that an operation on a class file
   * failed.
   */
  public static final String FILED_CLASS_FILE_OPERATION =
    "A file operation on the class file failed";

  /**
   * The message which informs that the current project has no class file output
   * location set.
   */
  public static final String DISAS_CLASSFILEOUTPUT_PROBLEMS =
    "The current project has no class file output location set";

  /**
   * The message which informs the user that a path does not exists.
   */
  public static final String DISAS_PATH_DOES_NOT_EXIST =
    "The path does not exist";

  /**
   * The message which informs the user that the editor cannot be created
   * or initialised.
   */
  public static final String DISAS_EDITOR_PROBLEMS =
    "The byte code editor cannot be opended or initialised";

  /**
   * The message which informs the user that the document does not contain
   * a line of the given number.
   */
  public static final String NO_LINE_IN_DOC =
    "The current document has no positions for the line ";

  /**
   * The message which informs the user that the document does not contain
   * a position of the given number.
   */
  public static final String NO_POSITION_IN_DOC =
    "The current document has no position ";

  /**
   * The message which informs the user that the document does not contain
   * a method of the given number.
   */
  public static final String NO_METHODS_IN_DOC =
    "The current document has too many methods (" + SUBSTITUTE + ")";

  /**
   * A template message that warns about wrong file type.
   */
  public static final String INVALID_EXTENSION =
    "This is not a \"" + SUBSTITUTE + "\" file.";

  /**
   * A template message that warns about wrong location in a document.
   */
  public static final String WRONG_LOCATION_MSG =
    "Wrong location " + SUBSTITUTE + " in a " + SUBSTITUTE2 + " document.";


  /**
   * The message informs the user that the synchronisation is impossible.
   */
  public static final String WRONG_SYNCHRONISATION_MSG =
    "This position cannot be synchronised.";

  /**
   * The message informs the user that access to a Java element is impossible.
   */
  public static final String WRONG_JAVAACCESS_MSG =
    "A Java element cannot be accessed.";

  /**
   * The message informs the user that the position cannot be associated with
   * an instruction in a reasonable way.
   */
  public static final String NOINSTRUCTION_MSG =
    "No source code instruction can be associated with the given position";

  /**
   * The empty constructor to forbid the creation of the instances.
   */
  private GUIMessages() {
  }

  /**
   * This method substitutes in the given message all the template points with
   * the given substitute string.
   *
   * @param a_message a message to substitute template positions
   * @param a_substitute a string to fill in the template positions
   * @return a string with the template positions properly substituted
   */
  public static String substitute(final String a_message,
                                  final String a_substitute) {
    return a_message.replaceAll(SUBSTITUTE, a_substitute);
  }

  /**
   * This method substitutes in the given message all the template points with
   * the given substitute string.
   *
   * @param a_message a message to substitute template positions
   * @param a_substitute a string to fill in the first kind of the template
   *   positions
   * @param a_substitute2 a string to fill in the second kind of the template
   *   positions
   * @return a string with the template positions properly substituted
   */
  public static String substitute2(final String a_message,
                                   final String a_substitute,
                                   final String a_substitute2) {
    return a_message.replaceAll(SUBSTITUTE, a_substitute).
                     replaceAll(SUBSTITUTE2, a_substitute2);
  }

  /**
   * This method displays error message for {@link UmbraRangeException}
   * signals.
   *
   * @param a_shell a shell which displays the messages
   * @param an_ex an exception which caused the need of the message
   * @param a_title a title of the message window
   */
  public static void exceededRangeInfo(final Shell a_shell,
                                       final UmbraRangeException an_ex,
                                       final String a_title) {
    final Exception e = an_ex.getCause();
    if (e instanceof UmbraLocationException) {
      final UmbraLocationException loce = (UmbraLocationException) e;
      MessageDialog.openError(a_shell, a_title,
                                    NO_LINE_IN_DOC +
                                    loce.getWrongLocation());
    } else if (e instanceof UmbraMethodException) {
      final UmbraMethodException methe = (UmbraMethodException) e;
      MessageDialog.openInformation(a_shell, a_title,
                                    NO_METHODS_IN_DOC.replaceAll(SUBSTITUTE,
                                    "" + methe.getWrongMethodNumber()));
    }
  }

  /**
   * Displays the message that the current project has no output path for
   * Java class files.
   *
   * @param a_shell the shell which displays the message
   * @param a_title the title of the message window
   */
  public static void wrongClassFileOptMessage(final Shell a_shell,
                                              final String a_title) {
    MessageDialog.openError(a_shell, a_title,
                            DISAS_CLASSFILEOUTPUT_PROBLEMS);
  }
}
