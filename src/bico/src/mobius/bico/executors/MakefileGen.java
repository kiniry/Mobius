package mobius.bico.executors;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;

/**
 * Generate the main makefile, the one at the root directory.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class MakefileGen {
  /** the base directory in which is the application compiled currently. */
  private final File fWorkingDir;


  /**
   * Initialize the generator.
   * @param baseDir the base directory
   */
  public MakefileGen(final File baseDir) {
    fWorkingDir = baseDir;
  }
  
  
  /**
   * Generates the makefile in the given directory.
   */
  public void generate() {

    final File mkfile = new File (fWorkingDir, "Makefile");
    try {
      final PrintStream out = new PrintStream(new FileOutputStream(mkfile));
      
      compileAll(out);
      compileExtras(out);
      compileBicolano(out);
      compileMain(out);
      compileSignature(out);
      compileType(out);
      out.println();
      implicitRule(out);
      
      out.close();
    } 
    catch (FileNotFoundException e) {
      System.err.println("Failed to write the Makefile");
      e.printStackTrace();
    }
     
  }

  /**
   * Compile the extra libraries.
   * This method is made to be overriden. In its former form
   * it does nothing.
   * @param out the output stream to write to the makefile
   */
  public void compileExtras(final PrintStream out) {
    
  }

  /**
   * The main compilation instructions. 
   * It is made to be overriden.
   * @param out the output stream to write to the makefile
   */
  public void compileAll(final PrintStream out) {
    out.println("\nall: bicolano main  ");
    out.println("\tcd classes; make all");
  }

  private void compileBicolano(final PrintStream out) {
    out.println("\nbicolano:");
    out.println("\t@echo ");
    out.println("\t@echo Making Bicolano");
    out.println("\t@echo ");
    out.println("\t@if [ -d Formalisation/Makefile ]; then cd Formalisation; make; fi");
  }

  private void compileMain(final PrintStream out) {
    out.println("\nmain: signature  ");
    out.println("\t@echo ");
    out.println("\t@echo Compiling the main files...");
    out.println("\t@echo ");
    out.println("\t@cd classes; make main");
    out.println("\tcoqc Bico.v");
  }

  private void implicitRule(final PrintStream out) {
    out.println("\n# implicit rules");
    out.println("%.vo : %.v");
    out.println("\tcoqc $<\n");
  }

  private void compileType(final PrintStream out) {
    out.println("\ntype: ");
    out.println("\t@echo ");
    out.println("\t@echo Compiling types...");
    out.println("\t@echo ");
    out.println("\t@cd classes; make type");
    out.println("\tcoqc Bico_type.v");
  }

  private void compileSignature(final PrintStream out) {
    out.println("\nsignature: type ");
    out.println("\t@echo ");
    out.println("\t@echo Compiling signatures...");
    out.println("\t@echo ");
    out.println("\t@cd classes; make signature");
    out.println("\tcoqc Bico_signature.v");
  }



}
