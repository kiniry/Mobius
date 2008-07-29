package mobius.bico;

import java.io.File;
import java.io.IOException;
import java.security.Permission;
import java.util.ArrayList;
import java.util.List;

import org.apache.bcel.Repository;
import org.apache.bcel.util.ClassPath;

import mobius.bico.Constants.Option;
import mobius.bico.executors.Executor;
import mobius.bico.implem.IImplemSpecifics;
import mobius.bico.implem.ListImplemSpecif;
import mobius.bico.implem.MapImplemSpecif;

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


  
  /**
   * Does nothing.
   */
  private Main() {
  
  }
  
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
    System.setSecurityManager(new SecurityManager() {
      public void checkPermission(final Permission perm) {
      }
    });
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
    IImplemSpecifics implem = new MapImplemSpecif();
    File baseDir = null;
    File targetDir = null;
    boolean generateLibs = false;
    ClassPath cp = null;
    final List<String> clzz = new ArrayList<String>();
    for (int i = 0; i < args.length; i++) {
      String arg = args[i];
      final Option opt = Option.translate(arg);
      switch (opt) {
        case LIST:
          implem = new ListImplemSpecif();
          break;
        case MAP:
          implem = new MapImplemSpecif();
          break;
        case CLASSPATH:
          i = i + 1;
          arg = args[i];
          cp = new ClassPath(arg);
          break;
        case OUTPUT:
          // this keyword introduces the base working class path
          i = i + 1;
          arg = args[i];
          targetDir = new File(arg);
          break;
        case LIB:
          generateLibs = true;
          i = i + 1;
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
            if (baseDir == null) {
              baseDir = f;
            }
          }
          else if ((f.exists()) || ((f.getParentFile() != null) &&
              f.getParentFile() .exists())) {
            clzz.add(f.getAbsolutePath()); 
          } 
          else  {
            // we suppose it's to be found in the class path
            clzz.add(arg); 
          }
          break;
      }
      
    }

    if (baseDir == null) {
      baseDir = new File("");
    }
    if (targetDir == null) {
      targetDir = baseDir;
    }
    if (cp == null) {
      cp = new ClassPath(baseDir.getAbsolutePath() + 
                  File.pathSeparatorChar + ClassPath.getClassPath());
    }

    return new Executor(implem, baseDir, targetDir, cp, clzz, generateLibs);
  }
}
