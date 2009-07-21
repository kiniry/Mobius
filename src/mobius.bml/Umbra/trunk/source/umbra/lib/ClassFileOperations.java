/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.lib;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaModelException;

import umbra.UmbraPlugin;

/**
 * @author alx
 * @version a-01
 *
 */
public class ClassFileOperations {

  /**
   * This method loads from the given Java class repository a class pointed out
   * by the given path.
   *
   * @param a_path a workspace relative path to the class file
   * @param a_repo the repository to load the class from
   * @param an_ol the output location for the class files
   * @return the BCEL {@link org.apache.bcel.classfile.JavaClass} structure with
   *   the content of the class file
   * @throws ClassNotFoundException in case the class cannot be loaded
   */
  public static JavaClass loadJavaClass(final IPath a_path,
                                  final SyntheticRepository a_repo,
                                  IPath an_ol)
    throws ClassNotFoundException {
    IPath np = a_path.removeFirstSegments(a_path.matchingFirstSegments(an_ol));
    final String clname = np.removeFileExtension().toOSString();
    if (FileNames.DEBUG_MODE)
      UmbraPlugin.messagelog("We open class: " + clname);
    return a_repo.loadClass(clname);
  }

  /**
   * The method gives the repository where all the class files associated
   * with the given project are located.
   *
   * @param a_jproject the project to find the class path for
   * @return the repository of the class files
   * @throws JavaModelException if the output location for the current project
   *   does not exist
   */
  public static SyntheticRepository getClassRepoForProject(
      final IJavaProject a_jproject)
    throws JavaModelException {
    //obtain the classpath for the classes
    final IPath outputloc = a_jproject.getOutputLocation().append("/-"); //bogus
    final String pathName = FileNames.getPath(outputloc).
                                               removeLastSegments(1).
                                               addTrailingSeparator().
                                               toPortableString();
    final ClassPath cp = new ClassPath(pathName);
    return SyntheticRepository.getInstance(cp);
  }
}
