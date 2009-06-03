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

import umbra.instructions.errors.BytecodeError;
import umbra.instructions.errors.ErrorReport;

/**
 * This is just container for texts of all the GUI messages.
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

  /**
   * A string to indicate a point in a string template where the
   * third portion of data to instantiate the template should be substituted.
   */
  public static final String SUBSTITUTE3 = "#3#";

  /* *********************************************************************
   * GUI MESSAGES
   */

  /**
   * A string used as an Umbra menu title.
   */
  public static final String BYTECODE_MENU_TITLE = "Bytecode";

  /**
   * A string used as a generic header in the message panes launched in
   * connection with the byte code text editor.
   */
  public static final String BYTECODE_MESSAGE_TITLE = "Bytecode";

  /**
   * A string used as a generic header in the message panes launched in
   * connection with the byte code verification.
   */
  public static final String VERIFICATION_MESSAGE_TITLE =
    "Bytecode verification";

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
   * A string used as a header in the message panes launched when the initial
   * parsing of a bytecode textual document is started.
   */
  public static final String INITIAL_PARSING_MESSAGE_TITLE =
    "Bytecode initial parsing";

  /**
   * A string used as a header in the message panes launched when the fragment
   * parsing is conducted.
   */
  public static final String FRAGMENT_PARSING_MESSAGE_TITLE =
    "Bytecode fragment parsing";

  /**
   * The message which informs the user that the operation he/she wants to
   * carry out cannot be performed.
   */
  public static final String INVALID_EDIT_OPERATION = "Invalid edit operation";

  /**
   * The message which informs the user that the document being edited is not
   * a bytecode document.
   */
  public static final String NOT_BYTECODE_DOCUMENT =
    "You are not editing a byte code document";

  /**
   * The message which requires the user to save the byte code before it
   * is disassembled.
   */
  public static final String SAVE_BYTECODE_FIRST =
    "You must save the source code before you can show its bytecode.";

  /**
   * The message which requires the user to save the bytecode and
   * source code before they are combined.
   */
  public static final String SAVE_BYTECODE_AND_SOURCE_FIRST =
    "You must save the source code and bytecode before combine action";

  /**
   * The message which informs the user that the file cannot be saved under
   * the given location.
   */
  public static final String DISAS_SAVING_PROBLEMS =
    "Problems with saving the file under the given location: " + SUBSTITUTE;

  /**
   * The message which informs the user that the Save As action is not
   * allowed.
   */
  public static final String SAVE_AS_NOT_ALLOWED =
    "Save As action is not allowed";

  /**
   * The message which informs the user that the copying from one place
   * to another is not possible.
   */
  public static final String COPY_IMPOSSIBLE =
    "The file \"" + SUBSTITUTE + "\" cannot be copied to " + SUBSTITUTE2;

  /**
   * The message requires the user to input the appropriate historical
   * version number.
   */
  public static final String VERSION_NUMBER_INFORMATION =
    "Input version number (" + SUBSTITUTE + " to " + SUBSTITUTE2 + "): " +
    SUBSTITUTE3;

  /**
   * The message which informs the user that the file cannot be saved under
   * the given location.
   */
  public static final String DISAS_LOADING_PROBLEMS =
    "Problems with loading the file under the given location: " + SUBSTITUTE;

  /**
   * The message which informs the user that the class file for the given
   * source code file cannot be saved.
   */
  public static final String DISAS_SAVEFORSOURCE_PROBLEMS =
    "Problems with saving a class file for the source code file: " + SUBSTITUTE;

  /**
   * The message which informs the user that an operation on a class file
   * failed.
   */
  public static final String FAILED_CLASS_FILE_OPERATION =
    "A file operation on the class file failed";

  /**
   * The message which informs the user that the plugin could not find the
   * given class.
   */
  public static final String CANNOT_FIND_CLASS =
    "Cannot find the class " + SUBSTITUTE + ".class";

  /**
   * The message which informs the user that a problem with a BML attribute
   * occurred.
   */
  public static final String BML_ATTRIBUTE_PROBLEM =
    "A BML attribute problem";

  /**
   * The message which informs the user that a problem with a BML attribute
   * occurred.
   */
  public static final String MALFORMED_MODIFICATION =
    "Wrong modification decription";

  /**
   * The message which informs the user that nothing has been modified
   * however it should have been.
   */
  public static final String NOTHING_MODIFIED =
    "Nothing has been modified";

  /**
   * The message which informs that the current project has no class file output
   * location set.
   */
  public static final String DISAS_CLASSFILEOUTPUT_PROBLEMS =
    "The current project has no class file output location set";

  /**
   * The message which informs that the current project has no class file output
   * location set.
   */
  public static final String CLASSPATH_PROBLEMS_MESSAGE =
    "Classpath cannot be properly resolved, empty classpath is used instead";

  /**
   * The message which informs the user that the class file for the given
   * source code file cannot be loaded.
   */
  public static final String DISAS_LOADFORSOURCE_PROBLEM =
    "Problems with loading a class file for the source code file: " +
    SUBSTITUTE;

  /**
   * The message which informs the user that the editor cannot be created
   * or initialised.
   */
  public static final String DISAS_EDITOR_PROBLEMS =
    "The byte code editor cannot be opended or initialised";

  /**
   * The message which informs the user that an improper Eclipse icon is
   * referenced.
   */
  public static final String IMPROPER_ICON =
    "Improper bytecode icon on eclipse GUI reference (" + SUBSTITUTE + ")";

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
   * The message which informs the user that the history of Umbra is
   * full.
   */
  public static final String HISTORY_FULL_MESSAGE =
    "History is already full";

  /**
   * The message which informs the user that the change of the colouring
   * is impossible.
   */
  public static final String COLOURING_REFRESH_IMPOSSIBLE_MESSAGE =
    "Cannot refresh the colouring";

  /**
   * The message which informs the user that the bytecode editor should be
   * refreshed.
   */
  public static final String REFRESH_REQUIRED =
    "The bytecode editor should be refreshed";

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
   * The message informs the user that the class file for the given source code
   * cannot be found.
   */
  public static final String NO_CLASS_FILE_FOR_SOURCE =
    "The class file corresponding to the Java source code file cannot be found";

  /**
   * The message informs the user that the class file for the path
   * cannot be found.
   */
  public static final String NO_CLASS_FILE_FOR_PATH =
    "The path " + SUBSTITUTE + " does not lead to a valid class file";

  /**
   * The message informs the user that the position cannot be associated with
   * an instruction in a reasonable way.
   */
  public static final String NOINSTRUCTION_MSG =
    "No source code instruction can be associated with the given position";

  /**
   * The message informs the user that the given value is not integer and
   * proposes a default value.
   */
  public static final String NOT_INTEGER_MESSAGE =
    "This is not an integer. " + "Should we use " + SUBSTITUTE + " instead?";

  /**
   * The message informs the user that the given value is not integer and
   * proposes a default value.
   */
  public static final String NOT_IN_RANGE_MESSAGE =
    "The number is not in the range " + "(" + SUBSTITUTE + " to " +
    SUBSTITUTE2 + "). Should we use " + SUBSTITUTE3 + " instead?";

  /**
   * The status bar information that the edit operation resulted in correct
   * code.
   */
  public static final String CORRECT_CODE = "Correct";

  /**
   * The status bar information that the edit operation resulted in incorrect
   * code.
   */
  public static final String INCORRECT_CODE = "Error detected: " + SUBSTITUTE;


  /**
   * The message informs the user that the operation led to inconsistency in
   * the internal representation of the bytecode.
   */
  public static final String REPRESENTATION_ERROR_MESSAGE =
    "Problem in establishing internal representation: " + SUBSTITUTE;

  /**
   * The message informs the user that the verification of bytecode ended
   * with error.
   */
  public static final String VERIFICATION_ERROR_MESSAGE =
    "Errors occured during bytecode verification. Save anyway?";

  /**
   * The empty constructor to forbid the creation of the instances.
   */
  private GUIMessages() {
  }

  /**
   * The message informs the user that errors in textual representation
   * of bytecode has been detected and list those errors.
   * @param a_report error report
   * @param an_error <code>true</code> if there are error in constant pool
   * that are not in error report
   * @return message
   */
  public static String constantPoolError(final ErrorReport a_report,
                                         final boolean an_error) {
    String message = "Following errors occured:\n";
    for (BytecodeError e : a_report.getErrors()) {
      message += e.getShortErrorMessage() + "\n";
    }
    if (an_error) message += "constant pool inconsistent\n";
    message += "Save anyway?";
    return message;
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
   * This method substitutes in the given message all the template points with
   * the given substitute string.
   *
   * @param a_message a message to substitute template positions
   * @param a_substitute a string to fill in the first kind of the template
   *   positions
   * @param a_substitute2 a string to fill in the second kind of the template
   *   positions
   * @param a_substitute3 a string to fill in the third kind of the template
   *   positions
   * @return a string with the template positions properly substituted
   */
  public static String substitute3(final String a_message,
                                   final String a_substitute,
                                   final String a_substitute2,
                                   final String a_substitute3) {
    return a_message.replaceAll(SUBSTITUTE, a_substitute).
                     replaceAll(SUBSTITUTE2, a_substitute2).
                     replaceAll(SUBSTITUTE3, a_substitute3);
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

  /**
   * This method pops up an appropriate error dialog informing
   * the user that a wrong location in a textual document is
   * reached. The kind of the message depends on the exception
   * in the parameter.
   *
   * @param a_shell a shell in which the dialog is popped up
   * @param a_title a title of the dialog to be popped up
   * @param an_ex the exception which triggered the error dialog
   */
  public static void messageWrongLocation(final Shell a_shell,
                     final String a_title,
                     final UmbraLocationException an_ex) {
    if (an_ex.isLineWrong()) {
      MessageDialog.openError(a_shell, a_title,
                            GUIMessages.NO_LINE_IN_DOC +
                            an_ex.getWrongLocation());
    } else {
      MessageDialog.openError(a_shell, a_title,
                              GUIMessages.NO_POSITION_IN_DOC +
                              an_ex.getWrongLocation());
    }
  }
}
