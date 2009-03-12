package mobius.bico;

import java.io.File;
import java.io.IOException;

import mobius.bico.Constants.Option;
import mobius.bico.executors.Executor;
import mobius.bico.executors.LaunchInfos;

import org.apache.bcel.Repository;

/**
 * The main class to launch bico!
 * 
 * @author J. Charles (julien.charles@inria.fr), P. Czarnik
 *         (czarnik@mimuw.edu.pl)
 */
public final class Main {
  /** Bico major version number. */
  public static final int MAJOR_VERSION = 0;
  /** Bico minor version number. */
  public static final int MINOR_VERSION = 6;
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
   */
  public static void main(final String[] args) throws IOException {
    System.out.println(WELCOME_MSG);
//    System.setSecurityManager(new SecurityManager() {
//      public void checkPermission(final Permission perm) {
//      }
//    });
    Executor exec;
    try {
      exec = init(args);
      // set the static  repository instance in class  
      // org.apache.bcel.Repository to the repository of 
      // the executor
      // this is done as seemingly some of the classes use this instance
      Repository.setRepository(exec.getRepository());
    } 
    catch (IllegalArgumentException e) {
      System.err.println(e.getMessage());
      System.err.println("(try java -jar bico.jar help)");
      return;
    }
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
   * @param args the arguments
   * @return a newly created executor.
   */
  private static Executor init(final String[] args) {
    // dealing with args
    // we first sort out arguments from path...
    /* final List<File> paths = new Vector<File>(); */
    final LaunchInfos li = new LaunchInfos();
    
    for (int i = 0; i < args.length; i++) {
      String arg = args[i];
      final Option opt = Option.translate(arg);
      if (opt.is2ArgsOption()) {
        i = i + 1;
        arg = args[i];
        switch (opt) {
          case CLASSPATH:
            li.setClassPath(arg);
            break;
          case OUTPUT:
            // this keyword introduces the base working class path
            li.setTargetDir(new File(arg));
            break;
          default:
            break;
        }
      }
      else {
        singleArgOptionsHandler(li, arg, opt);
      }
      
    }
    li.prepare();

    return new Executor(li);
  }

  /**
   * Treats all the options that have only a single argument, 
   * the option itself.
   * @param li the information structure where to save the options informations
   * @param arg the current inspected argument
   * @param opt the option which was selected.
   */
  private static void singleArgOptionsHandler(final LaunchInfos li,
                                              final String arg, final Option opt) {
    switch (opt) {
      case LIB:
        li.enableLibrariesGeneration();
        break;
      case LIST:
        System.err.println(LIST_MSG);
        li.setListImplementation();
        break;
      case MAP:
        //li.fImplem = new MapImplemSpecif();
        // the default cas anyway
        break;
      case HELP:
        System.out.println(HELP_MSG);
        break;  
      case UNKNOWN:
      default:
        final File f = new File(arg);
        if (f.isDirectory()) {
          // if the file f is a directory then this is the path at which 
          // all classes involved can be found setBaseDir(f); 
          li.setBaseDir(f);
        }
        else {
          li.addClassToTreat(arg);
        }
          
        break;
    }
  }
}
