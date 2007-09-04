package mobius.bico;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.List;

import mobius.bico.executors.ClassExecutor;

/**
 * Generates a makefile to compile everything
 * that was generated.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class MakefileGenerator {

  /** the directory where to generate the makefile. */
  private final File fBaseDir;
  /** the main files prefix. */
  private final String fBaseName;
  /** all the classes that were generated in the process. */
  private final List<ClassExecutor> fTreated;

  /**
   * Initialize the generator.
   * @param baseDir the base directory
   * @param baseName the name of the file 
   * @param treated all the classes to treat
   */
  public MakefileGenerator(final File baseDir, 
                           final String baseName, 
                           final List<ClassExecutor> treated) {
    fBaseDir = baseDir;
    fBaseName = baseName;
    fTreated = treated;
  }

  
  /**
   * Generates the makefile in the given directory.
   */
  public void generate() {
    final File mkfile = new File (fBaseDir, "Makefile");
    try {
      final PrintStream out = new PrintStream(new FileOutputStream(mkfile));
      out.println("all:");
      out.println("\t# Types compilation ");
      for (ClassExecutor ce: fTreated) {
        out.println("\tcoqc " + ce.getModuleFileName() + "_type.v");
      }
      out.println("\tcoqc " + fBaseName + "_type.v");
      
      out.println("\n\t# Signature compilation ");
      for (ClassExecutor ce: fTreated) {
        out.println("\tcoqc " + ce.getModuleFileName() + "_signature.v");
      }
      out.println("\tcoqc " + fBaseName + "_signature.v");
      
      out.println("\n\t# Main compilation ");
      for (ClassExecutor ce: fTreated) {
        out.println("\tcoqc " + ce.getModuleFileName() + ".v");
      }
      out.println("\tcoqc " + fBaseName + ".v");
      
      
      out.close();
    } 
    catch (FileNotFoundException e) {
      System.err.println("Failed to write the Makefile");
      e.printStackTrace();
    }
    
  }
  
}
