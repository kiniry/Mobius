/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.lib;

import java.io.File;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.Signature;
import org.eclipse.jdt.internal.ui.actions.SelectionConverter;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jdt.internal.ui.javaeditor.JavaEditor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.IFileEditorInput;


/**
 * This is just container for operations on the file names used in the Umbra
 * plugin (i.e. .java, .class, .btc). It contains the methods to convert
 * from one kind of name to another one with the whole logic.
 *
 * The logic of file location is as follows:
 * - the class files and all their historical versions should be kept where
 *   the output directory for the current project is
 * - the .btc files are located where the .java files are
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @author Krzysztof Jakubczyk (kjk@mimuw.edu.pl)
 * @version a-01
 */
public final class FileNames {

  /* *********************************************************************
   * FILE EXTENSIONS
   */

  /**
   * The file extension for the Java files.
   */
  public static final String JAVA_EXTENSION     = ".java";

  /**
   * The file extension for the Java class files, without dot.
   */
  public static final String CLASS_EXTENSION_NONDOT      = "class";

  /**
   * The file extension for the history files, without dot.
   */
  public static final String BYTECODE_HISTORY_EXTENSION_NONDOT   = "bt";

  /**
   * The file extension for the Java class files.
   */
  public static final String CLASS_EXTENSION    = ".class";

  /**
   * The file extension for the files with the Umbra bytecode representation
   * (i.e. .btc).
   */
  public static final String BYTECODE_EXTENSION   = ".btc";

  /**
   * The file extension for the files with the BoogiePL files
   * (i.e. .bpl).
   */
  public static final CharSequence BOOGIEPL_EXTENSION = ".bpl";

  /**
   * The file extension for the history files.
   */
  public static final String BYTECODE_HISTORY_EXTENSION   = ".bt";

  /**
   * This constant says if the debugging print outs should be generated.
   */
  public static final boolean DEBUG_MODE = true;

  /**
   * This constant says if the debugging print outs for CP should be generated.
   */
  public static final boolean CP_DEBUG_MODE = true;

  /**
   * A private empty constructor to prevent constructing of objects for this
   * class.
   */
  private FileNames() {
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
   * @param a_java_file Java source code file for which we try to find the
   *        class file
   * @param an_editor in which the .java file is edited
   * @return the IFile for the corresponding .class file
   * @throws JavaModelException in case the project in which the editor operates
   *   has no class file output location set
   */
  public static IFile getClassFileFile(final IFile a_java_file,
                     final IEditorPart an_editor)
    throws JavaModelException {
    return getClassFileFileFor(a_java_file, an_editor);
  }

  /**
   * This method gives the proper .btc file for a given
   * Java file or class file.
   *
   * @param a_file Java source code file for which we try to find the
   *        .btc file
   * @return the IFile for the corresponding .btc file
   */
  public static IFile getBTCFileName(final IFile a_file) {
    final String ext = a_file.getFullPath().getFileExtension();
    final String fname = replaceLast(a_file.getFullPath().
                                          toPortableString(),
                               ext, BYTECODE_EXTENSION.substring(1));
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
   * This method returns for a given path to a file with the extension
   * <code>an_extension</code> a name of the class file that was saved in order
   * to keep the original copy of the class file generated from the Java source
   * code file. No check is made that the path indeed has the extension.
   *
   * @param a_path a path to a file
   * @param an_extension the extension for which the orignal byte code file
   * name is returned
   * @return corresponding name of the file with the saved version of the
   * original byte code
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
   * This method gives the proper class file file for a given source
   * file (usually Java or .btc file).
   *
   * @param a_file a source code file for which we try to find the
   *   class file
   * @param an_editor a Java file editor in which the corresponding Java file
   *   is edited
   * @return the {@link IFile}for the corresponding .class file
   * @throws JavaModelException in case the project in which the editor operates
   *                            has no class file output location set
   */
  public static IFile getClassFileFileFor(final IFile a_file,
                     final IEditorPart an_editor)
    throws JavaModelException {
    
    final IProject project = ((IFileEditorInput) an_editor.getEditorInput()).getFile().getProject();
    final IJavaProject jproject = JavaCore.create(project);
    final IPath outputloc = jproject.getOutputLocation();
    final IPath elempath = a_file.getFullPath().
      removeFileExtension().addFileExtension(JAVA_EXTENSION.substring(1));
    final IPath nelempath = removeSourcePath(elempath,
                                             jproject.getRawClasspath());
    final ICompilationUnit elem =
      (ICompilationUnit) jproject.findElement(nelempath);
    final IType typ = elem.findPrimaryType();
    final String fqn = typ.getFullyQualifiedName();
    final IPath np = outputloc.append(fqn.replace(Signature.C_DOT,
                                            File.separatorChar)).
      addFileExtension(CLASS_EXTENSION.substring(1));
    final IWorkspace workspace = ResourcesPlugin.getWorkspace();
    final IFile file = workspace.getRoot().
             getFile(np);
    return file;
  }

  /**
   * The method removes the initial segments of the given path which
   * correspond to the source directory so that only the name of the
   * file with the path inside the source directory is left (package
   * name).
   *
   * @param an_epath a path to the file to remove the source path from
   * @param the_clpath the class path which contains the source path
   * @return the original path with the segments of the source directory
   *   removed or <code>null</code> in case no source folder matched
   *   the initial segment of the given path
   */
  private static IPath removeSourcePath(final IPath an_epath,
                                        final IClasspathEntry[] the_clpath) {
    for (int i = 0; i < the_clpath.length; i++) {
      final IClasspathEntry entry = the_clpath[i];
      if (entry.getEntryKind() == IClasspathEntry.CPE_SOURCE) {
        final IPath path = entry.getPath();
        if (path.isPrefixOf(an_epath)) {
          final int num = an_epath.matchingFirstSegments(path);
          return an_epath.removeFirstSegments(num);
        }
      }
    }
    return null;
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

  /**
   * This method returns java class file path file of a java element.
   * Proposed usage:
   *  getClassFilePath(getSelectedType(editor))
   * @param a_java_type type to find output class file path
   * @return output class file path
   * @throws JavaModelException if the output path for the current project does
   *  not exist
   */
  public static IPath getClassFilePath(final IType a_java_type)
    throws JavaModelException {
    return getOutputTypePath(a_java_type).append(a_java_type.
                                                 getUnderlyingResource().
                                                 getName())
        .removeFileExtension().addFileExtension(CLASS_EXTENSION_NONDOT);
  }

// Better, easier way, but VALID ONLY SINCE ECLIPSE VERSION 3.3
// usage: getClassFilePath2(getSelectedType(editor))
//  public static IPath getClassFilePath2(final IType element)
//        throws JavaModelException {
//    IJavaElement enclosingCompilationUnit = (ICompilationUnit)
//        element.getAncestor(IJavaElement.COMPILATION_UNIT);
//    IRegion region = JavaCore.newRegion();
//    region.add(enclosingCompilationUnit);
//    IResource[] ress = JavaCore.getGeneratedResources(region, false);
//    String originalName = element.getTypeQualifiedName() + CLASS_EXTENSION;
//    for(IResource resource: ress){
//      String resourceName = resource.getName();
//      if (resourceName.equals(originalName))
//        return resource.getProjectRelativePath();
//    }
//    return null;
//  }

  /**
   * Method returns output path (containing output .class files) of the
   * package where javaElement is situated.
   *
   * @param a_java_type the element to find output package of
   * @return package output path of javaElement
   * @throws JavaModelException if the output path for the current project does
   *  not exist
   */
  public static IPath getOutputTypePath(final IType a_java_type)
    throws JavaModelException {
    final IJavaProject project = a_java_type.getJavaProject();
    final IPath path = project.getOutputLocation();
    return path.append(a_java_type.getFullyQualifiedName().
                                   replace(Signature.C_DOT,
                                           File.separatorChar));
  }

  /**
   * This method returns a package of given IJavaElement.
   *
   * @param a_java_element the element we want to find package of
   * @return java package name
   */
  public static String getPackageName(final IJavaElement a_java_element) {
    final int elementType = a_java_element.getElementType();
    if (elementType == IJavaElement.PACKAGE_FRAGMENT ||
        elementType == IJavaElement.PACKAGE_FRAGMENT_ROOT) {
      return a_java_element.getElementName();
    } else {
      return a_java_element.getAncestor(IJavaElement.PACKAGE_FRAGMENT)
          .getElementName();
    }
  }

  /**
   * Method returns IJavaElement associated with IEditorPart.
   *
   * @param an_editor the editor to get IJavaElement from
   * @return java element associated with editor
   */
  public static IJavaElement getJavaElement(final IEditorPart an_editor) {
    final IEditorInput editorInput = an_editor.getEditorInput();
    return (IJavaElement) editorInput.getAdapter(IJavaElement.class);
  }

  /**
   * Method returns enclosing IType for IJavaElement.
   *
   * @param a_java_element the IJavaElement
   * @return enclosing IType of javaElement
   */
  public static IType getEnclosingType(final IJavaElement a_java_element) {
    return (IType) a_java_element.getAncestor(IJavaElement.TYPE);
  }

  /**
   * Method returns the selected IType in IEditorPart.
   *
   * @param an_editor the editor to find IType. IMPORTANT: must be JavaEditor.
   * @return IType selected in editor
   * @throws JavaModelException if the contents of the editor
 *    cannot be accessed
   */
  public static IType getSelectedType(final IEditorPart an_editor)
    throws JavaModelException {
    final IJavaElement element = SelectionConverter.getElementAtOffset(
                                         (JavaEditor) an_editor);
    IType type = FileNames.getEnclosingType(element);
    if (type == null) {
      final ICompilationUnit elem =
                                  (ICompilationUnit) getJavaElement(an_editor);
      type = elem.findPrimaryType();
    }
    return type;
  }

  /**
   * Transform a relative file path (inside the project) into the absolute one.
   *
   * @param a_path a relative path
   * @return the corresponding absolute path
   */
  public static IPath getPath(final IPath a_path) {
    return ResourcesPlugin.getWorkspace().getRoot().getFolder(a_path).
                           getLocation();
  }
}
