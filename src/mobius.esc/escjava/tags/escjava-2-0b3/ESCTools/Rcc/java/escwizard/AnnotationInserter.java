/* Copyright 2000, 2001, Compaq Computer Corporation */

// ESC/Java annotation wizard, annotation inserter
// Copyright (c) 1999, Compaq Computer Corporation
// Change history:
//    2 Apr 1999  rustan     Created

package escwizard;

import java.io.File;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;


public class AnnotationInserter {
  //@ requires elemsnonnull(args);
  public static void main(String[] args) {
    if (args.length == 1 && args[0].equals("-ping")) {
      return;
    }
    if (args.length < 2) {
      error("usage: AnnotationInserter instructionFile [-f <file of sourcefiles>] sourcefiles...");
    }
    File instructionFile = new File(args[0]);
    String instructions = new String(FileInfo.getFileContents(instructionFile)); // TODO: check this (rgrig)!
    FileCollection sources = new FileCollection(2*(args.length-1));
    for (int i = 1; i < args.length; i++) {
      if (args[i].equals("-f")) {
        try {
          i++; // yes, it's the loop counter.
          //@ assume i < args.length;
          BufferedReader in = 
            new BufferedReader(new FileReader(args[i]));
          String s;
          while ((s = in.readLine()) != null) {
            sources.add(s);
          }
        } catch (IOException e) {
          System.out.println(e.toString());
          System.exit(1);
        } 
      } else {
        sources.add(args[i]);
      }
    }

    for (int i = 0; i < instructions.length(); ) {
      iCurrentLine++;
      int k = instructions.indexOf('\n', i);
      if (i == -1) {
        error(args[0] + " does not end with newline");
      }
      String instr = instructions.substring(i, k);
      process(instr, sources);
      i = k+1;
    }

    sources.update();
  }

  static int iCurrentLine = 0;

  //@ ensures false;
  static void error(/*@ non_null */ String s) {
    System.out.println("AnnotationInserter: " + s +
                       " [instruction " + iCurrentLine + "]");
    System.exit(1);
  }

  static void process(/*@ non_null */ String instr,
                      /*@ non_null */ FileCollection sources) {
    Instr ii = Instr.make(instr, sources);
    // System.out.println("@@ " + ii.toString());  System.out.flush();
    WorkItem wi = ii.process(sources);
    if (wi == null) {
      // System.out.println("## null");  System.out.flush();
    } else { 
      // System.out.println("## " + wi.toString());  System.out.flush();
      FileInfo fi = sources.getFileInfo(wi.fileid);
      //@ assume fi.data != null;
      fi.addWorkItem(wi);
    }
  }
}
