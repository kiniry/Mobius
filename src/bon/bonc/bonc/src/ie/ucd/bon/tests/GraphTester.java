/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.tests;

import ie.ucd.bon.Main;

public class GraphTester {

  public static void main(String[] args) {

    boolean timing = false;
    if (args.length > 0 && args[0].equalsIgnoreCase("timing=true")) {
      timing = true;
    }

    String testDir = "../test/";
    String outputDir = testDir + "graph/";

    String[] testFiles = {"typingtest"};

    for (String s : testFiles) {
      printGraph(testDir, s, outputDir, timing);
    }
  }

  public static void printGraph(String fileDir, String fileName, String outputDir, boolean timing) {
    String margs = "";
    if (timing) {
      margs += "-time ";
    }
    margs += "-cg " + outputDir + fileName + ".dot" + " " + fileDir + fileName;

    Main.main(margs.split("\\s+"));

  }
}
