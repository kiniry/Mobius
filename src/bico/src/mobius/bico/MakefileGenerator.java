package mobius.bico;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import mobius.bico.executors.ClassExecutor;

/**
 * Generates a makefile to compile everything
 * that was generated.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class MakefileGenerator {

  /** the base directory in which is the application compiled currently */
  private final File fBaseDir;
  /** the main files prefix. */
  private final String fBaseName;
  /** all the classes that were generated in the process. */
  private final List<ClassExecutor> fTreated;
  /**where to generate the makefile.*/
  private final String pck;

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
    pck = null;
  }
  
  
  /**
   * Initialize the generator.
   * @param baseDir the base directory
   * @param baseName the name of the file 
   * @param treated all the classes to treat
   */
  public MakefileGenerator(final File _baseDir, String _pckg) {
    fBaseDir = _baseDir;
    pck = _pckg;
    fBaseName = null;
    fTreated = null;
  }
  

  
  /**
   * Generates the makefile in the given directory.
   */
  public void generate() {
    final File mkfile = new File (new File(fBaseDir, pck), "Makefile");
    final List<String> generatedFiles = new ArrayList<String>();
    
    try {
      final PrintStream out = new PrintStream(new FileOutputStream(mkfile));

      generatedFiles.addAll(printCompileInstr(out, "Type", "_type"));
      generatedFiles.addAll(printCompileInstr(out, "Signature", "_signature"));
      generatedFiles.addAll(printCompileInstr(out, "Main", ""));
      generatedFiles.addAll(getExtraGeneratedFiles(out));
      
      
/*      out.println("all:  $(Extra)");
      out.println("$(Extra): $(Main)");*/
      out.println("all:  $(Main)");
      out.println("$(Main): $(Signature)"); 
      out.println("$(Signature): $(Type)"); 

      out.println("\nclean:");
      out.print("\trm -f");
      for (String name: generatedFiles) {
        out.print(" " + name);
      }
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


  /**
   * Writes the compilation instructions for the extra files.
   * @param out the make file were to print the commands
   * @return the list of files that are supposed to be generated
   */
  protected List<String> getExtraGeneratedFiles(final PrintStream out) {
    out.println("Extra= ");
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
	  File[] files = new File(fBaseDir, pck).listFiles();
		if (files == null) {
			return null;
		}

		String recmake = "";
		final List<String> generatedFiles = new ArrayList<String>();
		out.print(word + "=");
		for (int k = 0; k < files.length; k++) { 
			if (files[k].isFile()) {
				String fName = files[k].getName();
				String coqModuleName = Util.coqify(pck + fName);
				String filename = coqModuleName + postfix + ".vo";
			    out.print(" " + filename);
			    generatedFiles.add(filename);
			} else if (files[k].isDirectory()) {
			    recmake = "cd" + files[k].getName() + " && " + "$(MAKE) all";
			    
			}
			
		} 
		out.println();
		out.println(recmake);
   /* final List<String> generatedFiles = new ArrayList<String>();
    String filename;
    out.print(word + "=");
    for (ClassExecutor ce: fTreated) {
      filename = ce.getModuleFileName() + postfix + ".vo";
      out.print(" " + filename);
      generatedFiles.add(filename);
    }
    filename = fBaseName + postfix + ".vo";
    out.print(" " + filename);
    generatedFiles.add(filename);
    out.println();*/
    return generatedFiles;
  }
  
}
