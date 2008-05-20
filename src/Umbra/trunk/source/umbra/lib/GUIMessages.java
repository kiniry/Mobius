/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.lib;

/**
 * This is just container for texts of all the GUI messages.
 *
 * TODO: this does not contain all the messages
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
   * A string used as a header in the message panes launched in connection
   * with the Java source code action to disassemble code (class
   * {@ref DisasBCEL}).
   */
  public static final String DISAS_MESSAGE_TITLE =
    "Disassemble Bytecode";

  /**
   * A string used as a header in the message panes launched in connection
   * with the Java source code action to synchronisation code (classes
   * {@link umbra.java.actions.SynchrSBAction} and
   * {@link umbra.editor.actions.BytecodeSynchrAction}.
   */
  public static final String SYNCH_MESSAGE_TITLE =
    "Synchronisation";

  /**
   * A string used as a header in the message panes launched in connection
   * with the bytecode action to translate the bytecode to BoogiePL (class
   * {@ref BytecodeToBoogiePLAction}).
   */
  public static final String B2BPL_MESSAGE_TITLE =
    "Bytecode To BoogiePL";

  /**
   * The message which requires the user to save the bytecode before it
   * is disassembled.
   */
  public static final String DISAS_SAVE_BYTECODE_FIRST =
    "You must save the source code before you can show its bytecode.";

  /**
   * The message which informs the user that the file cannot be saved under
   * the given location.
   */
  public static final String DISAS_SAVING_PROBLEMS =
    "Problems with saving the file under the given location";

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
   * The message which requires the user to save the bytecode before it is
   * translated to BoogiePL.
   */
  public static final String B2BPL_SAVE_BYTECODE_FIRST =
    "You must save the bytecode before you can translate it into BoogiePL.";

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
    "No instruction can be associated with the given position";

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

}
