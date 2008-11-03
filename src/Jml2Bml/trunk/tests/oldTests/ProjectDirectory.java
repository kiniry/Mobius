/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-06 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package oldTests;

import java.io.File;
import java.io.IOException;

/**
 * Class contains constant containing current directory, - useful for tests.
 * @author kjk (kjk@mimuw.edu.pl)
 *
 * @version 0-0.1
 */
public final class ProjectDirectory {

  /** Current directory constant. */
  public static final String PROJECT_DIR = getCurrentDir();

  /**
   * This class is static.
   */
  private ProjectDirectory() {
  };

  /**
   * Method gets current working directory.
   * @return current canonical path string
   */
  private static String getCurrentDir() {
    final File dir = new File(".");
    try {
      return dir.getCanonicalPath();
    } catch (IOException e) {
      e.printStackTrace();
      return "Error";
    }
  }

}
