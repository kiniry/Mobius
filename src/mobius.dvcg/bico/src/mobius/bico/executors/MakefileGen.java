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
      setEnv(out);
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
   * Prints in the output strean all the environment variables.
   * @param out the output stream where to write
   */
  public static final void setEnv(final PrintStream out) {
    out.println("COQC=coqc\n");
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
    out.println();
    printRule(out, "all", "bicolano main",
              new String[] {"cd classes; make all"});
  }

  /**
   * Instructions to compile Bicolano if its
   * makefiles exist. 
   * @param out the makefile to output the directives
   */
  private static void compileBicolano(final PrintStream out) {
    out.println();
    printRule(out, "bicolano", "",
              new String[] {"@echo ",
                            "@echo Making Bicolano",
                            "@echo ",
                            "@if [ -d Formalisation/Makefile ]; " +
                                "then cd Formalisation; make; fi"});
              
  }

  /**
   * Compiles the main files, the Bico.v file and the Class.v files.
   * @param out the makefile to output the directives
   */
  private static void compileMain(final PrintStream out) {
    out.println();
    printRule(out, "main", "signature", 
              new String[] {"@echo ",
                            "@echo Compiling the main files...",
                            "@echo ",
                            "@cd classes; make main",
                            "$(COQC) Bico.v"});
  }

  /**
   * The implicit rule at the end of the makefile,
   * to compile the coq files.
   * @param out the makefile to output the directives
   */
  public static void implicitRule(final PrintStream out) {
    out.println();
    out.println("# implicit rules");
    printRule(out, "%.vo ", "%.v",
              new String[] {"$(COQC) $<\n"});
  }

  /**
   * The rules to compile the type files (all the
   * files ending with _type.v).
   * @param out the makefile to output the directives
   */
  private static void compileType(final PrintStream out) {
    out.println();
    printRule(out, "type", "",
              new String[] {"@echo ",
                            "@echo Compiling types...",
                            "@echo ",
                            "@cd classes; make type",
                            "$(COQC) Bico_type.v"});
  }

  /**
   * Rules to compile signature files (the file ending with
   * _signature.v).
   * @param out the makefile to output the directives
   */
  private static void compileSignature(final PrintStream out) {
    final String [] actions = {"@echo ",
                               "@echo Compiling signatures...",
                               "@echo ",
                               "@cd classes; make signature",
                               "$(COQC) Bico_signature.v"};
    
    out.println();
    printRule(out, "signature", "type", actions);
  }
  
  /**
   * Prints a makefile rule to the specific stream.
   * It has the following form:
   * <pre>
   * name: dependencies
   *    action1
   *    action2
   *    action3
   *    ...
   * </pre>
   * @param out the stream to write to
   * @param name the name of the rule
   * @param dependencies the dependencies
   * @param actions the list of actions.
   */
  public static void printRule(final PrintStream out, final String name, 
                               final String dependencies, final String[] actions) {
    out.println(name + ": " + dependencies);
    for (String s: actions) {
      out.println("\t" + s);
    }
  }
}
