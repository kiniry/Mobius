/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.tests;

import ie.ucd.bon.Main;

public class TypeCheckerTester {


  public static void main(String[] args) {

    boolean timing = false;
    if (args.length > 0 && args[0].equalsIgnoreCase("timing=true")) {
      timing = true;
    }

    String testDir = "../test/";

    String[] testFiles = { "typingtest" };

    for (String s : testFiles) {
      typeCheck(testDir + s, timing);
    }
  }

  public static void typeCheck(String filePath, boolean timing) {
    //File f = new File(filePath);

    String margs = "";
    if (timing) {
      margs += "-time ";
    }
    margs += "-tc " + filePath;

    Main.main(margs.split("\\s+")); 

  }
}

