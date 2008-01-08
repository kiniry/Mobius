/*
 * @title       "Jml2Bml"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2008-01-07 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package jml2bml.bytecode;

import java.io.File;

/**
 * Class representing the .class file location.
 *
 * @author kjk (kjk@mimuw.edu.pl)
 *
 */
public class ClassFileLocation {
  /**
   * Directory name.
   */
  private final String dirName;

  /**
   * The qualified name of the class (with packages).
   */
  private final String classQualifiedName;

  public ClassFileLocation(String dirName, String classQualifiedName) {
    this.dirName = dirName;
    this.classQualifiedName = classQualifiedName;
  }

  public String getDirectoryName(){
    return dirName;
  }

  public String getClassQualifiedName(){
    return classQualifiedName;
  }

  public String getClassFilePath(){
    return dirName + File.separator +
    classQualifiedName.replace('.', File.separatorChar) + ".class";
  }
}
