/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.tests;

import ie.ucd.bon.Main;

import java.io.File;

public class ParsingTester {


  public static void main(String[] args) {

    String testDir = "../test/test-examples/";

    testDirectory(new File(testDir));
  }

  public static void testDirectory(File directory) {
    File[] testFiles = directory.listFiles();

    for (File f : testFiles) {
      testFile(f);
    }
  }

  public static void testFile(File file) {
    if (file.getName().startsWith(".")) {
      return;
    }
    if (file.isDirectory()) {
      testDirectory(file);
    } else {
      System.out.println("Testing parsing on file: " + file);
      String[] args = {"-ntc", "-time", file.getAbsolutePath()};
      Main.main(args);
    }

  }


}
