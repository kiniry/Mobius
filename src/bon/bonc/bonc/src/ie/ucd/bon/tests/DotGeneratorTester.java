/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.tests;

import ie.ucd.bon.Main;

import java.io.File;

public class DotGeneratorTester {
  public static void main(String[] args) {

    boolean timing = false;
    if (args.length > 0 && args[0].equalsIgnoreCase("timing=true")) {
      timing = true;
    }

    String testDir = "../test/";
    String outDir = "../test/dot/";
    //TODO we should be creating this dir if necessary... (can do in ant for moment...)

    printDotForAllInDirTo(testDir, outDir, timing);
  }

  public static void printDotForAllInDirTo(String originalFilesDir, String outputDir, boolean timing) {
    File[] files = new File(originalFilesDir).listFiles();

    for (File f : files) {
      if (!f.getName().startsWith(".") && !f.isDirectory()) {
        String margs = "";
        if (timing) {
          margs += "-time ";
        }
        margs += "-p dot -po " + outputDir + " " + originalFilesDir + f.getName();

        Main.main(margs.split("\\s+"));
      }
    }
  }


}



