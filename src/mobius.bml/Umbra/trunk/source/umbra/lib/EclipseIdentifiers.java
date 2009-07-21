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
 * This is just a container for textual Eclipse identifiers of objects defined
 * in Umbra.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public final class EclipseIdentifiers {


  /* *********************************************************************
   * ECLIPSE TEXTUAL IDENTIFIERS
   */

  /**
   * The text editor extension identifier which identifies the Umbra
   * bytecode editor.
   */
  public static final String BYTECODE_EDITOR_CLASS =
    "umbra.BytecodeEditor";

  /**
   * The contribution identifier which identifies the Umbra contribution to
   * Eclipse GUI.
   */
  public static final String BYTECODE_CONTRIBUTION_IDENTIFIER = "Bytecode";

  /**
   * The menu identifier which identifies the menu with Umbra bytecode
   * actions.
   */
  public static final String UMBRA_BYTECODE_MENU = "umbra.bytecodeMenu";

  /**
   * The postion after which Umbra bytecode menu is added.
   */
  public static final String MENU_POSITION = "additions";

  /**
   * The identifier of the history group within the bytecode menu.
   */
  public static final String HISTORY_GROUP = "historyGroup";

  /**
   * The identifier of the color group within the bytecode menu.
   */
  public static final String COLOR_GROUP = "colorGroup";

  /**
   * The end of line sequence for editor.
   */
  public static final String EDITOR_EOL = "\n";

  /* *********************************************************************
   * ACTION NAMES
   */

  /**
   * The name of the restore action.
   *
   * @see umbra.editor.actions.history.BytecodeRestoreAction
   */
  public static final String RESTORE_ACTION_NAME = "Restore";

  /**
   * The name of the clear history action.
   *
   * @see umbra.editor.actions.history.ClearHistoryAction
   */
  public static final String CLEAR_HISTORY_ACTION_NAME = "Clear history";

  /**
   * The name of the history action.
   *
   * @see umbra.editor.actions.history.HistoryAction
   */
  public static final String HISTORY_ACTION_NAME = "Add to history";

  /**
   * The name of the colour action.
   *
   * @see umbra.editor.actions.BytecodeColorAction
   */
  public static final String COLOR_ACTION_NAME = "Change color";

  /**
   * The name of the combine action.
   *
   * @see umbra.editor.actions.BytecodeCombineAction
   */
  public static final String COMBINE_ACTION_NAME = "Combine";

  /**
   * The name of the rebuild action.
   *
   * @see umbra.editor.actions.BytecodeRebuildAction
   */
  public static final String REBUILD_ACTION_NAME = "Rebuild";

  /**
   * The name of the refresh action.
   *
   * @see umbra.editor.actions.BytecodeRefreshAction
   */
  public static final String REFRESH_ACTION_NAME = "Refresh";

  /**
   * The name of the synchronise action.
   *
   * @see umbra.editor.actions.BytecodeSynchrAction
   */
  public static final String SYNCHRONIZE_ACTION_NAME = "Synchronize";

  /**
   * The name of the action which runs the verification through BoogiePL.
   *
   * @see umbra.editor.actions.BytecodeSynchrAction
   */
  public static final String GENBPL_ACTION_NAME = "BoogiePL";

  /**
   * The empty constructor to forbid the creation of the instances.
   */
  private EclipseIdentifiers() {
  }

}
