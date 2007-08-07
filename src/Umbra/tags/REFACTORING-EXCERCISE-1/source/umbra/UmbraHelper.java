/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.AbstractTextEditor;


/**
 * This is just container for common operations used in the
 * application.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public final class UmbraHelper {

  /**
   * A string to indicate a point in a string template where the
   * data to instantiate the template should be substituted.
   */
  public static final String SUBSTITUTE = "{1}";

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

  /* *********************************************************************
   * FILE EXTENSIONS
   */

  /**
   * The file extension for the Java files.
   */
  public static final String JAVA_EXTENSION     = ".java";

  /**
   * The file extension for the Java class files.
   */
  public static final String CLASS_EXTENSION    = ".class";

  /**
   * The file extension for the files with the Umbra bytecode representation.
   */
  public static final String BYTECODE_EXTENSION   = ".btc";

  /**
   * The file extension for the history files.
   */
  public static final String BYTECODE_HISTORY_EXTENSION   = ".bt";

  /**
   * The extension for BoogiePL files.
   */
  public static final String BOOGIEPL_EXTENSION = ".bpl";


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
    "You must save the bytecode before you can disassemble it.";

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
   * The text editor extension identifier which identifies the BoogiePL
   * editor.
   */
  public static final String BOOGIEPL_EDITOR_CLASS =
    "umbra.BoogiePLEditor";

  /**
   * A private empty constructor to prevent constructing of objects for this
   * class.
   */
  private UmbraHelper() {
  }

  /**
   * This method replaces the last occurrence of the <code>oldSuffix</code>
   * with the <code>newSuffix</code> in <code>string</code>. It serves to
   * exchange the file sufficies. In case <code>oldSuffix</code> does not
   * occur in <code>string</code> it returns <code>string</code>.
   *
   * @param a_string string to replace the suffix from
   * @param an_old_suffix the suffix to replace
   * @param a_new_suffix the new suffix
   * @return the string with replaced suffix
   */
  public static String replaceLast(final String a_string,
                   final String an_old_suffix,
                   final String a_new_suffix) {
    if (a_string.endsWith(an_old_suffix)) {
      // Return string with new suffix
      return a_string.substring(0, a_string.lastIndexOf(an_old_suffix)).
                        concat(a_new_suffix);
    } else {
      // Given suffix does not occur
      return a_string;
    }
  }

  /**
   * This is a convenience method to obtain the classpath
   * separator relevant to the current operating system.
   *
   * @return the string that separates the classpath entries
   */
  public static String getClassPathSeparator() {
    return System.getProperty("path.separator");
  }

  /**
   * This is a convenience method to obtain the separator
   * that separates subsequent direcotry and file entries
   * in a path to a resource. This value is relevant to the current
   * operating system.
   *
   * @return the string that separates the file path entries
   */
  public static String getFileSeparator() {
    return System.getProperty("file.separator");
  }

  /**
   * This method strips off all the whitespace characters
   * in the given string even inside the string.
   *
   * @param a_strip_me the string to strip the whitespace from
   * @return the string with the whitespace stripped off
   */
  public static String stripAllWhitespace(final String a_strip_me) {
    String s;
    s = "";
    int ii = 0;
    final int jj = a_strip_me.length();
    for (ii = 0; ii < jj; ii++)
      if (!(Character.isWhitespace(a_strip_me.charAt(ii)))) {
        s += a_strip_me.charAt(ii);
      }
    return s;
  }

  /**
   * This method gives the proper classfile file for a given
   * Java file.
   *
   * XXX Isn't there an eclipse method to do this task?
   *
   * @param a_java_file Java source code file for which we try to find the
   *        class file
   * @param an_editor in which the .java file is edited
   * @return the IFile for the corresponding .class file
   * @throws JavaModelException in case the project in which the editor operates
   *                            has no classfile output location set
   */
  public static IFile getClassFileFile(final IFile a_java_file,
                     final CompilationUnitEditor an_editor)
    throws JavaModelException {
    return getClassFileFileFor(a_java_file, an_editor, JAVA_EXTENSION);
  }

  /**
   * This method gives the proper .btc file for a given
   * Java file.
   *
   * @param a_file Java source code file for which we try to find the
   *        .btc file
   * @param an_editor in which the .java file is edited
   * @return the IFile for the corresponding .btc file
   */
  public static IFile getBTCFileName(final IFile a_file,
                                     final CompilationUnitEditor an_editor) {
    final String fname = replaceLast(a_file.getFullPath().
                                          toPortableString(),
                               JAVA_EXTENSION, BYTECODE_EXTENSION);
    final IWorkspace workspace = ResourcesPlugin.getWorkspace();
    return workspace.getRoot().getFile(Path.fromPortableString(fname));
  }

  /**
   * This method returns for a given path to a .btc file a name of the
   * classfile that was saved in order to keep the original copy of the
   * classfile generated from the Java source code file. No check is made that
   * the path <code>a_path</code> indeed has the extension.
   *
   * @param a_path a path to a .btc file
   * @return corresponding name of the file with the saved version of the
   * original bytecode
   */
  public static String getSavedClassFileNameForBTC(final IPath a_path) {
    return getSavedClassFileNameForPrefix(a_path, BYTECODE_EXTENSION);
  }

  /**
   * This method returns for a given path to a .bpl file a name of the
   * classfile that was saved in order to keep the original copy of the
   * classfile generated from the Java source code file. No check is made that
   * the path indeed has the extension.
   *
   * @param a_path a path to a .bpl file
   * @return corresponding name of the file with the saved version of the
   * original bytecode
   */
  public static String getSavedClassFileNameForBPL(final IPath a_path) {
    return getSavedClassFileNameForPrefix(a_path, BOOGIEPL_EXTENSION);
  }

  /**
   * This method returns for a given path to a file with the extension
   * <code>an_extension</code> a name of the classfile that was saved in order
   * to keep the original copy of the classfile generated from the Java source
   * code file. No check is made that the path indeed has the extension.
   *
   * @param a_path a path to a file
   * @param an_extension the extension for which the orignal bytecode file
   * name is returned
   * @return corresponding name of the file with the saved version of the
   * original bytecode
   */
  public static String getSavedClassFileNameForPrefix(final IPath a_path,
                                                  final String an_extension) {
    final String lastSegment = replaceLast(a_path.lastSegment(),
                                           an_extension,
                                           CLASS_EXTENSION);
    final String fnameTo = a_path.removeLastSegments(1).
                                  append("_" + lastSegment).toPortableString();
    return fnameTo;

  }

  /**
   * This method returns for a given path to a .class file a name of the
   * classfile that was saved in order to keep the original copy of the
   * classfile generated from the Java source code file. No check is made that
   * the path indeed has the extension.
   *
   * @param a_path a path to a .class file
   * @return corresponding name of the file with the saved version of the
   * original bytecode
   */
  public static String getSavedClassFileNameForClass(final IPath a_path) {
    return getSavedClassFileNameForPrefix(a_path, CLASS_EXTENSION);
  }

  /**
   * This method gives the proper classfile file for a given source
   * file (usually Java or .btc file).
   *
   * XXX Isn't there an eclipse method to do this task?
   *
   * @param a_java_file a source code file for which we try to find the
   *   class file
   * @param an_editor a Java file editor in which the corresponging Java file
   *   is edited
   * @param an_extension an extension of the file for which we generate
   *   the .class file name (usually .java or .btc)
   * @return the {@link IFile}for the corresponding .class file
   * @throws JavaModelException in case the project in which the editor operates
   *                            has no classfile output location set
   */
  public static IFile getClassFileFileFor(final IFile a_java_file,
                     final AbstractTextEditor an_editor,
                     final String an_extension)
    throws JavaModelException {
    final IProject project = ((FileEditorInput)an_editor.
        getEditorInput()).getFile().getProject();
    final IJavaProject jproject = JavaCore.create(project);
    final IPath outputloc = jproject.getOutputLocation();
    final String newloc = outputloc.append(a_java_file.getFullPath().
              removeFirstSegments(1)).toPortableString();
    final String fname = replaceLast(newloc, an_extension, CLASS_EXTENSION);
    final IWorkspace workspace = ResourcesPlugin.getWorkspace();
    final IFile file = workspace.getRoot().
             getFile(Path.fromPortableString(fname));
    return file;
  }

  /**
   * The method finds the first occurrence of the pattern
   * <code>a_pattern</code> in the string <code>the_data</code> and returns
   * the index of the first character after the occurrence of the pattern.
   * In case the pattern does not occur in the data string, the method
   * returns a negative number.
   *
   * @param the_data the string in which we seek the index
   * @param a_pattern a pattern we look for
   * @return the index of the first character after the first occurrence of
   *         the pattern; in case the pattern does not occur - a negative
   *         number
   */
  public static int getIndexAfter(final String the_data,
                                  final String a_pattern) {
    if (the_data.contains(a_pattern))
      return (the_data.indexOf(a_pattern) + a_pattern.length());
    else
      return -1;
  }
}
