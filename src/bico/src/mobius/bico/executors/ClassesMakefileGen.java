package mobius.bico.executors;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import mobius.bico.Util;

/**
 * Generates a makefile to compile everything
 * that was generated.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class ClassesMakefileGen {

  /** the base directory in which is the application compiled currently. */
  private final File fBaseDir;
  /** all the classes that were generated in the process. */
  private final List<ClassExecutor> fTreated = new ArrayList<ClassExecutor>();


  /**
   * Initialize the generator.
   * @param baseDir the base directory
   * @param treated all the classes to treat
   */
  public ClassesMakefileGen(final File baseDir, 
                           final Collection<ClassExecutor> treated) {
    fBaseDir = new File(baseDir, "classes");
    fTreated.addAll(treated);
  }
  
  /**
   * Generates the makefile in the given directory.
   */
  public void generate() {
    generate("");
  }
  
  private void generate(String pkgDir) {
    final File workingDir = new File(fBaseDir, pkgDir);
    final File mkfile = new File (workingDir, "Makefile");
    final List<String> generatedFiles = new ArrayList<String>();
    
    
    final File[] subdirs = workingDir.listFiles(new Util.DirectoryFilter());
    try {
      final PrintStream out = new PrintStream(new FileOutputStream(mkfile));
      final List<String> list = getCurrentPkgFileList(workingDir);
      generatedFiles.addAll(printCompileInstr(out, list, "Type", "_type"));
      generatedFiles.addAll(printCompileInstr(out, list, "Signature", "_signature"));
      generatedFiles.addAll(printCompileInstr(out, list, "Main", ""));
      generatedFiles.addAll(getExtraGeneratedFiles(out));
      
      out.println("\nall: main $(Extra) ");
      for (File dir: subdirs) {
        out.println("\tcd " + dir.getName() + "; make all");
      }
      out.println("\nmain: signature $(Main) ");
      for (File dir: subdirs) {
        out.println("\tcd " + dir.getName() + "; make all");
      }
      
      out.println("\nsignature: type $(Signature)");
      for (File dir: subdirs) {
        out.println("\tcd " + dir.getName() + "; make signature");
      }
      
      
      out.println("\ntype: $(Type)");
      for (File dir: subdirs) {
        out.println("\tcd " + dir.getName() + "; make type");
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
     

    for (File dir: subdirs) {
      generate(pkgDir + dir.getName() + File.separator);
    }
  }


  private List<String> getCurrentPkgFileList(File workingDir) {
    final List<String> list = new ArrayList<String>();
    for (ClassExecutor ce: fTreated) {
      if (ce.getWorkingDir().equals(workingDir)) {
        list.add(ce.getModuleName());
      }
    }
    return list;
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
   * @param list the list of the modules to compile
   * @param word the word in the comment describing what is done
   * @param postfix the postfix element of the name
   * @return the files that should be generated
   * by the compilation
   */
  public List<String> printCompileInstr(final PrintStream out,
                                         final List<String> list,
                                         final String word,
                                         final String postfix) {
    
    final File[] files = fBaseDir.listFiles();
    if (files == null) {
      return null;
    }
    
    final List<String> generatedFiles = new ArrayList<String>();
    out.print(word + "=");
    for (String coqModuleName: list) {
      //final String name = coqModuleName + postfix + ".v";
      final String filename = coqModuleName + postfix + ".vo";
      out.print(" " + filename);
      generatedFiles.add(filename);
    }

    out.println();

    return generatedFiles;
  }
  
}
