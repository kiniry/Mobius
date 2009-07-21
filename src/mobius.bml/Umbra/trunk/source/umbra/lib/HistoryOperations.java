/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.lib;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;


/**
 * This class implements the operations on history items. It implements the
 * operations to save and load historical versions of .btc files and .class
 * files.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public final class HistoryOperations {

  /**
   * The maximal number of history snapshots.
   */
  public static final int MAX_HISTORY = 2;

  /**
   * The minimal number of history snapshots.
   */
  public static final int MIN_HISTORY = 0;

  /**
   * The default value of the history number, used in case none is given or
   * in case an invalid number is used.
   */
  public static final int DEFAULT_HISTORY = 0;
  /**
   * A private empty constructor to prevent constructing of objects for this
   * class.
   */
  private HistoryOperations() {
  }

  /**
   * This method saves under the history slot number in <code>a_hist_num</code>
   * the bytecode classfile that corresponds to the file in
   * <code>a_file_from</code>. The editor is given to make the interface
   * compatible with
   * {@link #saveClassHistoryFile(IFile, int, CompilationUnitEditor)}.
   *
   * @param a_file_from a .btc file for which the class file is to be inserted
   *    into the history
   * @param a_hist_num a history slot number under which the file should
   *    be saved
   * @param an_editor editor which edits the Java file corresponding to the
   *    Java file
   * @throws CoreException in case the file system operations cannot be
   *   performed
   */
  public static void saveBTCHistoryFile(final IFile a_file_from,
                                   final int a_hist_num,
                                   final CompilationUnitEditor an_editor)
    throws CoreException {
    final IFile fileTo = getHistoryBTCFile(a_file_from, a_hist_num);
    fileTo.delete(true, null);
    a_file_from.copy(fileTo.getFullPath(), true, null);
  }

  /**
   * Obtains the historical version of the given .btc {@link IFile}.
   *
   * @param a_file_from a .btc file to retrieve the historical version for
   * @param a_hist_num the number of the item to retrieve from the history
   * @return the historical version of the file
   */
  private static IFile getHistoryBTCFile(final IFile a_file_from,
                                         final int a_hist_num) {
    return getHistoryFile(a_file_from, a_hist_num,
                          FileNames.BYTECODE_HISTORY_EXTENSION_NONDOT);
  }

  /**
   * Obtains the historical version of a file with the given extension for
   * the given .btc {@link IFile}. It removes the extension from the
   * given .btc file and replaces it with the given extension concatenated with
   * the historical item number.
   *
   * @param a_file_from a .btc file to retrieve the historical version for
   * @param a_hist_num the number of the item to retrieve from the history
   * @param an_ext the extension of the resulting file
   * @return  the historical version of the file with the given extension
   */
  private static IFile getHistoryFile(final IFile a_file_from,
                                      final int a_hist_num,
                                      final String an_ext) {
    final IPath active = a_file_from.getFullPath();
    final String ext = an_ext + a_hist_num;
    final IPath noext = active.removeFileExtension();
    final IPath pathTo = noext.addFileExtension(ext);
    final IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
    return root.getFile(pathTo);
  }

  /**
   * This method saves under the history slot number in <code>a_hist_num</code>
   * the bytecode classfile that corresponds to the file in
   * <code>a_file_from</code>.
   *
   * @param a_file_from a .btc file for which the classfile is to be inserted
   *    into the history
   * @param a_hist_num a history slot number under which the file should
   *    be saved
   * @param an_editor editor which edits the Java file corresponding to the
   *   Java file
   * @throws CoreException  in case the file system operations cannot be
   *   performed
   */
  public static void saveClassHistoryFile(final IFile a_file_from,
                                    final int a_hist_num,
                                    final CompilationUnitEditor an_editor)
    throws CoreException {
    final IFile classFrom = FileNames.getClassFileFileFor(a_file_from,
                                              an_editor);
    final IFile classTo = getHistoryClassFile(a_file_from, a_hist_num);
    classTo.delete(true, null);
    classFrom.copy(classTo.getFullPath(), true, null);
  }

 /**
  * Obtains the historical version of the class file for the given .btc
  * {@link IFile}.
  *
  * @param a_file_from a .btc file to retrieve the historical version for
  * @param a_hist_num the number of the item to retrieve from the history
  * @return the historical version of the file
  */
  private static IFile getHistoryClassFile(final IFile a_file_from,
                                       final int a_hist_num) {
    return getHistoryFile(a_file_from, a_hist_num,
                          FileNames.CLASS_EXTENSION_NONDOT);
  }

  /**
   * This method loads from the history slot number in <code>a_hist_num</code>
   * the .btc
   * file that corresponds to the file in
   * <code>a_file_from</code>. The editor is given to make the interface
   * compatible with
   * {@link #saveClassHistoryFile(IFile, int, CompilationUnitEditor)}.
   *
   * @param a_file_from a .btc file for which the .btc file is to be loaded
   *    from the history
   * @param a_hist_num a history slot number from which the file should
   *    be loaded
   * @param an_editor editor which edits the Java file corresponding to the
   *    Java file
   * @throws CoreException in case the file system operations cannot be
   *   performed
   */
  public static void loadBTCHistoryFile(final IFile a_file_from,
                                        final int a_hist_num,
                                        final CompilationUnitEditor an_editor)
    throws CoreException {
    final IFile histFile = getHistoryBTCFile(a_file_from, a_hist_num);
    a_file_from.delete(true, null);
    histFile.copy(a_file_from.getFullPath(), true, null);
  }

  /**
   * This method loads from the history slot number in <code>a_hist_num</code>
   * the class
   * file that corresponds to the .btc file in
   * <code>a_file_from</code>. The editor is given to make the interface
   * compatible with
   * {@link #saveClassHistoryFile(IFile, int, CompilationUnitEditor)}.
   *
   * @param a_file_from a .btc file for which the class file is to be loaded
   *    from the history
   * @param a_hist_num a history slot number from which the file should
   *    be loaded
   * @param an_editor editor which edits the Java file corresponding to the
   *    Java file
   * @throws CoreException in case the file system operations cannot be
   *   performed
   */
  public static void loadClassHistoryFile(final IFile a_file_from,
                                       final int a_hist_num,
                                       final CompilationUnitEditor an_editor)
    throws CoreException {
    final IFile classFile = FileNames.getClassFileFileFor(a_file_from,
                               an_editor);
    final IFile histClassFile = getHistoryClassFile(a_file_from, a_hist_num);
    classFile.delete(true, null);
    histClassFile.copy(classFile.getFullPath(), true, null);
  }

  /**
   * This method removes from the history slot number in <code>a_hist_num</code>
   * the .btc
   * file that corresponds to the file in
   * <code>a_file_from</code>. The editor is given to make the interface
   * compatible with
   * {@link #saveClassHistoryFile(IFile, int, CompilationUnitEditor)}.
   *
   * @param a_file_from a .btc file for which the .btc file is to be removed
   *    from the history
   * @param a_hist_num a history slot number from which the file should
   *    be removed
   * @param an_editor editor which edits the Java file corresponding to the
   *    Java file
   * @throws CoreException in case the file system operations cannot be
   *   performed
   */
  public static void removeBTCHistoryFile(final IFile a_file_from,
                                          final int a_hist_num,
                                          final CompilationUnitEditor an_editor)
    throws CoreException {
    final IFile histFile = getHistoryBTCFile(a_file_from, a_hist_num);
    histFile.delete(true, null);
  }

  /**
   * This method removes from the history slot number in <code>a_hist_num</code>
   * the class
   * file that corresponds to the .btc file in
   * <code>a_file_from</code>. The editor is given to make the interface
   * compatible with
   * {@link #saveClassHistoryFile(IFile, int, CompilationUnitEditor)}.
   *
   * @param a_file_from a .btc file for which the class file is to be removed
   *    from the history
   * @param a_hist_num a history slot number from which the file should
   *    be removed
   * @param an_editor editor which edits the Java file corresponding to the
   *    Java file
   * @throws CoreException in case the file system operations cannot be
   *   performed
   */
  public static void removeClassHistoryFile(final IFile a_file_from,
                                         final int a_hist_num,
                                         final CompilationUnitEditor an_editor)
    throws CoreException {
    final IFile histClassFile = getHistoryClassFile(a_file_from, a_hist_num);
    histClassFile.delete(true, null);
  }

}
