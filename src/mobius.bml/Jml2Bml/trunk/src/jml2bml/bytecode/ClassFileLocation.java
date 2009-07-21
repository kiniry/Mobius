/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-07 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.bytecode;

import java.io.File;

/**
 * Class representing the .class file location.
 *
 * @author kjk (kjk@mimuw.edu.pl)
 * @version 0.0-1
 */
public class ClassFileLocation {
  /**
   * Directory name.
   */
  private final String directoryName;

  /**
   * The qualified name of the class (with packages).
   */
  private final String classQualifiedName;

  /**
   * Constructor.
   * @param dirName directory name
   * @param qualifiedName qualified name of the class
   */
  public ClassFileLocation(final String dirName, final String qualifiedName) {
    this.directoryName = dirName;
    this.classQualifiedName = qualifiedName;
  }

  /**
   * Getter of the directory name.
   * @return directory name
   */
  public String getDirectoryName() {
    return directoryName;
  }

  /**
   * Getter of the class qualified name.
   * @return class qualified name
   */
  public String getClassQualifiedName() {
    return classQualifiedName;
  }

  /**
   * Returns path to class file.
   * @return path to class file
   */
  public String getClassFilePath() {
    return directoryName + File.separator +
           classQualifiedName.replace('.', File.separatorChar) + ".class";
  }
}
