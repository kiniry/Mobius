package mobius.bico.executors;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import mobius.bico.Util;

public class MakefileGen {
  /** the base directory in which is the application compiled currently. */
  private final File fWorkingDir;
  /** all the classes that were generated in the process. */
  private final List<ClassExecutor> fTreated = new ArrayList<ClassExecutor>();


  /**
   * Initialize the generator.
   * @param baseDir the base directory
   * @param treated all the classes to treat
   */
  public MakefileGen(final File baseDir) {
    fWorkingDir = baseDir;
//    fTreated.addAll(treated);
  }
  
  /**
   * Generates the makefile in the given directory.
   */
  public void generate() {

    final File mkfile = new File (fWorkingDir, "Makefile");
    
    
    final File[] subdirs = fWorkingDir.listFiles(new Util.DirectoryFilter());
    try {
      final PrintStream out = new PrintStream(new FileOutputStream(mkfile));
      
      out.println("\nall: bicolano main $(Extra) ");
      out.println("\tcd classes; make all");
      
      out.println("\nbicolano:");
      out.println("\t@echo ");
      out.println("\t@echo Making Bicolano");
      out.println("\t@echo ");
      out.println("\t@cd Formalisation; make");
      
      out.println("\nmain: signature  ");
      out.println("\t@echo ");
      out.println("\t@echo Compiling the main files...");
      out.println("\t@echo ");
      out.println("\t@cd classes; make main");
      out.println("\tcoqc Bico.v");
      
      out.println("\nsignature: type ");
      out.println("\t@echo ");
      out.println("\t@echo Compiling signatures...");
      out.println("\t@echo ");
      out.println("\t@cd classes; make signature");
      out.println("\tcoqc Bico_signature.v");
      
      out.println("\ntype: ");
      out.println("\t@echo ");
      out.println("\t@echo Compiling types...");
      out.println("\t@echo ");
      out.println("\t@cd classes; make type");
      out.println("\tcoqc Bico_type.v");
      

      out.println();
      out.println("\n# implicit rules");
      out.println("%.vo : %.v");
      out.println("\tcoqc $<\n");
      out.close();
    } 
    catch (FileNotFoundException e) {
      System.err.println("Failed to write the Makefile");
      e.printStackTrace();
    }
     
  }



}
