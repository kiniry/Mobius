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
  
  /**
   * Generates the makefile in the given package directory
   * given by the argument.
   * @param pkgDir the package directory
   */
  private void generate(final String pkgDir) {
    final File workingDir = new File(fBaseDir, pkgDir);
    if (!workingDir.exists() &&
         !workingDir.mkdirs()) {
      System.err.println("Failed to create the working directory " +
                         workingDir + "!");
      return;
    }
    
    final File mkfile = new File (workingDir, "Makefile");
    
    final File[] subdirs = workingDir.listFiles(new Util.DirectoryFilter());
    try {
      final PrintStream out = new PrintStream(new FileOutputStream(mkfile));
      MakefileGen.setEnv(out);
      final List<String> list = getCurrentPkgFileList(workingDir);
      getMakefileInstructions(out, subdirs, list);
      out.println("\n");
      MakefileGen.implicitRule(out);
      out.close();
    } 
    catch (FileNotFoundException e) {
      System.err.println("Failed to write the Makefile " + mkfile.getAbsolutePath());
      e.printStackTrace();
    }
     
    for (File dir: subdirs) {
      generate(pkgDir + dir.getName() + File.separator);
    }
  }

  /**
   * Print all the makefile rules.
   * @param out the output file.
   * @param subdirs the subdirectories to treat
   * @param listModule the list 
   * @return the files that will be generated during compilation
   */
  public List<String> getMakefileInstructions(final PrintStream out, 
                                              final File[] subdirs, 
                                              final List<String> listModule) {
    final List<String> generatedFiles = new ArrayList<String>();
    
    
    
    printMakeInstr(out, "all", "main", subdirs);
    
    generatedFiles.addAll(
      printCompileInstr(out, listModule, subdirs, 
                        "Type", "", "_type"));
    generatedFiles.addAll(
      printCompileInstr(out, listModule, subdirs, 
                        "Signature", "type", "_signature"));
    generatedFiles.addAll(
      printCompileInstr(out, listModule, subdirs, 
                        "Main", "signature", ""));
    return generatedFiles;
  }
  
  
  /**
   * Print the compile instructions of a specific rule.
   * @param out the output file
   * @param listModules the list of the modules to compile
   * @param subdirs the subdirectories to inspect
   * @param word the name of the files to compile
   * @param dependencies on which other rule the files depend
   * @param postfix what is the postfix part of the files
   * @return files that will be generated during the compilation process
   */
  public List<String> printCompileInstr(final PrintStream out,
                                        final List<String> listModules,
                                        final File[] subdirs,
                                        final String word,
                                        final String dependencies,
                                        final String postfix) {
    final List<String> files  = (printCompileInstr(out, listModules, word, postfix));
    printMakeInstr(out, word.toLowerCase(), dependencies + " $(" + word + ")", subdirs);
    return files;
  
  }
  /**
   * Print a make file instruction to the given stream.
   * @param out the makefile stream
   * @param name the label of this compilation clause
   * @param dependencies the dependencies of the label
   * @param subdirs the subdirectories to compile recursively
   */
  public void printMakeInstr(final PrintStream out,
                              final String name, 
                              final String dependencies, 
                              final File[] subdirs) {
    out.println("\n" + name + ": " + dependencies);
    for (File dir: subdirs) {
      out.println("\tcd " + dir.getName() + "; make " + name);
    }
    
  }

  /**
   * Get all the classes that should be in the given working directory.
   * @param workingDir the working directory to inspect
   * @return the list of the module name of the classes
   * in the working directory
   */
  private List<String> getCurrentPkgFileList(final File workingDir) {
    final List<String> list = new ArrayList<String>();
    for (ClassExecutor ce: fTreated) {
      if (ce.getWorkingDir().equals(workingDir)) {
        list.add(ce.getModuleName());
      }
    }
    return list;
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
