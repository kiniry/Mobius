/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.tests;

import ie.ucd.bon.Main;

import java.io.File;

public class ParsingTester {


  public static void main(String[] args) {

    String testDir = "../test/";
    //String testDir = "/home/fintan/workspace/ebon/docs/examples/";

    testDirectory(testDir);
  }
  
  public static void testDirectory(String directory) {
    String[] testFiles = new File(directory).list();
    
    for (String s : testFiles) {
      testFile(s, directory);
    }    
  }
  
  public static void testFile(String fileName, String directory) {
    if (fileName.startsWith(".") || new File(directory + fileName).isDirectory()) {
      return;
    }
    System.out.println("Testing parsing on file: " + fileName + " (" + directory + fileName + ")");
    String[] args = { "-time", directory + fileName };
    Main.main(args);
    
  }


}
