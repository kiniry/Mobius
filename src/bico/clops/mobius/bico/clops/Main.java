package mobius.bico.clops;

import ie.ucd.clops.runtime.automaton.AutomatonException;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;
import ie.ucd.clops.runtime.options.InvalidOptionValueException;

import java.io.IOException;

import mobius.bico.executors.Executor;
import mobius.bico.executors.LaunchInfos;
import mobius.bico.clops.BicoOptionsInterface;
import mobius.bico.clops.BicoParser;

import org.apache.bcel.Repository;

/**
 * The main class to launch bico!
 * This version uses UCD's CLOPS.
 * 
 * @author J. Charles (julien.charles@inria.fr), P. Czarnik
 *         (czarnik@mimuw.edu.pl)
 */
public final class Main {
  /** Bico major version number. */
  public static final int MAJOR_VERSION = 0;
  /** Bico minor version number. */
  public static final int MINOR_VERSION = 7;
  /** Bico revision version number = bug fix.  */
  public static final int REVISION_VERSION = 0;
  /** BICO version. */
  public static final String WELCOME_MSG = "BICO version " + 
        MAJOR_VERSION + "." + MINOR_VERSION + "rev" + REVISION_VERSION;
  
  /** the help message. */
  public static final String HELP_MSG = 
    "------------------------------------------------------------------------------------\n" + 
    "Bico converts *.class files into Coq format\n" + 
    "The default behaviour being to generate the files for Bicolano's \n" + 
    "implementation with maps.\n" + 
    "Its use is 'java -jar bico.jar Args'\n" + 
    "Args being a combination of the following arguments:\n" + 
    "<directory> - specify directory in which Bico does its job (there must be only one \n" + 
    "              directory, and this argument is mandatory)\n" + 
    "help        - it prints this help message\n" + 
    "-list       - forces the use of lists (incompatible with the -map argument)\n" + 
    "-map        - forces the use of maps (incompatible with the -list argument)\n" + 
    "<classname> - generates also the file for this class, bico must be able to find it \n" + 
    "              in its class path\n" + 
    "-----------------------------------------------------------------------------------";
  
  /** the list warning message. */
  public static final String LIST_MSG =
    "The list functionnality is not a trustable feature at this very moment.\n" +
    "If you want support for it please file a bug report on the Mobius Trac Server\n" +
    "http://mobius.ucd.ie/\n";
  /** */
  private Main() { }
  
  /**
   * Bico main entry point.
   * 
   * @param args
   *            the program arguments
   * @throws IOException
   *             if the is an error while creating the files
   * @throws InvalidOptionValueException 
   * @throws AutomatonException 
   */
  public static void main(final String[] args) throws IOException, AutomatonException, InvalidOptionValueException {
    System.out.println(WELCOME_MSG);
    Executor exec;
    
    BicoParser parser;
    try {
      parser = new BicoParser();
    } 
    catch (InvalidOptionPropertyValueException e) {
      e.printStackTrace();
      return;
    }
    if (!parser.parse(args)) {
      System.err.println("Bad usage!");
      System.err.println("(try java -jar bico.jar -help)");
      return;
    }
    final BicoOptionsInterface opt = parser.getOptionStore();
    
    if (opt.isHelpSet()) {
      System.out.println(HELP_MSG);
      return;
    }
    exec = init(opt);
  
    Repository.setRepository(exec.getRepository());
    
    try {
      exec.start();
    } 
    catch (ClassNotFoundException e) {
      e.printStackTrace();
      System.err.println(e.getMessage() + "\n" + 
                         "It was specified as a file to load... " +
                         "it should be in the class path!");
    }
  }
  
  /**
   * Init the executor with the arguments from the command line.
   * 
   * @param opt the option store containing the parsed options
   * @return a newly created executor. 
   */
  private static Executor init(final BicoOptionsInterface opt) {
    final LaunchInfos li = new LaunchInfos();

    if (opt.isListSet()) {
      System.err.println(LIST_MSG);
      li.setListImplementation();
    }
    
    li.setBaseDir(opt.getDir());
    li.setTargetDir(opt.getOutput());
    
    if (opt.getClassPath() != null) {
      li.setClassPath(opt.getClassPath());
    }
    
    for (String cl: opt.getClazz()) {
      li.addClassToTreat(cl);
    }
    if (opt.isLibSet()) {
      li.enableLibrariesGeneration();
    }
    li.prepare();

    return new Executor(li);
  }
}
