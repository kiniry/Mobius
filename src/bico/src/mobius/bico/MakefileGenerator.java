package mobius.bico;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
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
    final List<String> generatedFiles = new ArrayList<String>();
    
    try {
      final PrintStream out = new PrintStream(new FileOutputStream(mkfile));
      out.println("all:");
      generatedFiles.addAll(printCompileInstr(out, "Type", "_type"));
      generatedFiles.addAll(printCompileInstr(out, "Signature", "_signature"));
      generatedFiles.addAll(printCompileInstr(out, "Main", ""));
      generatedFiles.addAll(getExtraGeneratedFiles(out));
      out.println("\nclean:");
      out.print("\trm -f");
      for (String name: generatedFiles) {
        out.print(" " + name);
      }
      out.println();
      
      out.close();
    } 
    catch (FileNotFoundException e) {
      System.err.println("Failed to write the Makefile");
      e.printStackTrace();
    }
    
  }


  protected List<String> getExtraGeneratedFiles(PrintStream out) {
    return new ArrayList<String>();
  }


  /**
   * Print the compile instruction.
   * @param out the output stream to the makefile
   * @param word the word in the comment describing what is done
   * @param postfix the postfix element of the name
   * @return the files that should be generated
   * by the compilation
   */
  public List<String> printCompileInstr(final PrintStream out,
                                         final String word,
                                         final String postfix) {
    final List<String> generatedFiles = new ArrayList<String>();
    out.println("\t# " + word + " compilation ");
    String filename;
    for (ClassExecutor ce: fTreated) {
      filename = ce.getModuleFileName() + postfix + ".v";
      out.println("\tcoqc " + filename);
      generatedFiles.add(filename + "o");
    }
    filename = fBaseName + postfix + ".v";
    out.println("\tcoqc " + filename);
    generatedFiles.add(filename + "o");
    return generatedFiles;
  }
  
}
