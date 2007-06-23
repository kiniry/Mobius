package mobius.bico;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.security.Permission;
import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import mobius.bico.dico.CamlDictionary;
import mobius.bico.dico.Dictionary;
import mobius.bico.implem.IImplemSpecifics;
import mobius.bico.implem.ListImplemSpecif;
import mobius.bico.implem.MapImplemSpecif;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;


/**
 * The main entry point to bico.
 * @author J. Charles (julien.charles@inria.fr), 
 * P. Czarnik (czarnik@mimuw.edu.pl), 
 * L. Hubert (laurent.hubert@irisa.fr)
 */
public class Executor extends ABasicExecutor {
  /** BICO version 0.5. */
  public static final String WELCOME_MSG = "BICO version 0.5";

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

  /** determine the span of the 'reserved' packages names number default is 10. */
  private static final int RESERVED_PACKAGES = 10;


  /** the name of the output file. */
  private File fFileName;


  /** classes to be parsed from standard library. */
  private final List<String> fOtherLibs = new ArrayList<String>();

  /** classes to be read from hand-made files. */
  private final String[] fSpecialLibs = {"java.lang.Object", "java.lang.Throwable",
                                         "java.lang.Exception", "java.lang.String" };

  /** list of already treated classes. */
  private List<String> fTreatedClasses = new ArrayList<String>();
  
  /** list of already treated interfaces. */
  private List<String> fTreatedInterfaces = new ArrayList<String>();
  


  /** current package number. */
  private int fCurrentPackage = RESERVED_PACKAGES;

  /** tells whether or not the help message must be shown. */
  private boolean fShowHelp;

  /** the current working directory, where to generate the files. */ 
  private File fWorkingDir;
  
  /**
   * Minimal constructor.
   */
  private Executor() {
    super(SyntheticRepository.getInstance(), new MapImplemSpecif(),
          new MethodHandler(), null, new CamlDictionary());
  }

  /**
   * Parses the arguments given in the parameter. Each argument is in one cell
   * of the array, as in a {@link #main(String[])} method. Mainly initialize
   * all the private variables from <code>Executor</code>
   * 
   * @param args The argument given to <tt>bico</tt>
   */
  public Executor(final String[] args) {
    this();
    
    init(args);
    
  }
  
  /**
   * Create a new Executor object.
   * @param implem specify the implementation to use
   * @param workingDir the current working dir
   * @param outFile the output file
   * @param classToTreat the list of classes to treat
   */
  public Executor(final IImplemSpecifics implem, final File workingDir, 
                  final File outFile, final List<String> classToTreat) {
    this();
    fImplemSpecif = implem;
    fWorkingDir = workingDir;
    fFileName = outFile;
    fOtherLibs.addAll(classToTreat);
  }
  
  /**
   * Init the executor with the arguments from the command line.
   * @param args the arguments
   */
  private void init(final String [] args) {
     // dealing with args

    // we first sort out arguments from path...
    final List<File> paths = new Vector<File>();
    
    for (String arg: args) {
      final String low = arg.toLowerCase();
      if (low.equals("help")) {
        fShowHelp = true;
      } 
      else if (low.equals("-list")) {
        fImplemSpecif = new ListImplemSpecif();
      } 
      else if (low.equals("-map")) {
        fImplemSpecif = new MapImplemSpecif();
      }
      else {
        final File f = new File(arg);
        if ((f.exists()) || 
            ((f.getParentFile() != null) && f.getParentFile().exists())) {
          paths.add(f);
        } 
        else {
          // we suppose it's to be found in the class path
          fOtherLibs.add(arg);
        }
      }
    }
    
    initWorkingDir(paths);
  }
  
  
  
  /**
   * Initialize the working directory and file from the given path.
   * @param path the path list containing the directory.
   */
  private void initWorkingDir(final List<File> path) {
    if (path.size() > 1) {
      throw new IllegalArgumentException("It looks bad. " + 
                                         "You have specified to many valid paths " +
                                         "to handle: \n" + path + 
                                         "\nChoose only one, then come back!");
    }
    else if (path.size() == 0) {
      throw new IllegalArgumentException("You must specify at least one directory " +
          "to write the output file into...");
    }

    final File pathname = path.get(0);
    fWorkingDir = pathname; 
    if (!pathname.isDirectory()) {
      fWorkingDir = pathname.getParentFile();
    }
    

    fFileName = new File(fWorkingDir, 
                        fImplemSpecif.getFileName(Util.coqify(pathname.getName())) + ".v");
    System.out.println("Output file: " + fFileName);
  }

  /**
   * Launch bico !
   * 
   * @throws IOException
   *             in case of any I/O errors....
   * @throws ClassNotFoundException
   *             if libraries file specified in {@link #fOtherLibs} cannot be
   *             found
   */
  public void start() throws ClassNotFoundException, IOException {
    if (fShowHelp) {
      System.out.println(HELP_MSG);
    }
    
    System.out.println("Using " + fImplemSpecif + ".");
    System.out.println("Working path: " + fWorkingDir);
    // creating file for output
    if (fFileName.exists()) {
      fFileName.delete();
      System.err.println("previous file is being overwritten...");
    }
    fFileName.createNewFile();
    final FileOutputStream fwr = new FileOutputStream(fFileName);
    fOut = new PrintStream(fwr);

    // write prelude ;)
    doBeginning();

    // handle library classes specified as 'the other libs'
    
    for (String current: fOtherLibs) {
      System.out.println("Handling: " + current);
      handleLibraryClass(current);
    }

    final List<String> files = findFiles();
    // handle the found classes
    for (String current: files) {
      System.out.println("Handling: " + current);
      handleDiskClass(current, fFileName.getParent());
    }

    doEnding();

    fOut.close(); // closing output file
    
    writeDictionnary();
  }

  /**
   * Write the dictionnary to a file.
   * @throws IOException If there is a problem in writing.
   */
  private void writeDictionnary() throws IOException {
    final File dicoFile = new File(fWorkingDir, "dico.ml");
    fOut = new PrintStream(new FileOutputStream(dicoFile));
    fDico.write(fOut);
    fOut.close();
  }

  /**
   * Scan for classes in the current directory.
   * @return a list of class files found in the current directory
   */
  private List<String> findFiles() {
    // FIXME: should not be needed
    final List<String> files = new ArrayList<String>();
    final File f = fFileName.getParentFile();
    final String[] list = f.list();
    
    for (String current: list) {
      if (current.endsWith(".class")) {
        final int pom = current.indexOf(".");
        files.add(current.substring(0, pom));
      }
    }
    System.out.println("Found " + files.size() + " class file(s) in the working path.");
    return files;
  }

  /**
   * Bico main entry point.
   * @param args the program arguments
   * @throws IOException if the is an error while creating the files
   */
  public static void main(final String[] args) throws IOException {
    System.out.println(WELCOME_MSG);
    System.setSecurityManager(new SecurityManager() {
      public void checkPermission(final Permission perm) {
      }
    });
    Executor exec;
    try {
      exec = new Executor(args);
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
          "It was specified as a file to load... it should be in the class path!");
    }
  }

  /**
   * Handle one class from library files.
   * @param clname the class to load from the classpath
   * @throws ClassNotFoundException if the specified class cannot be found
   * @throws IOException if the class executor has a writing problem
   */
  public void handleLibraryClass(final String clname) throws ClassNotFoundException, 
                                                             IOException {
    System.out.println(clname);
    handleClass(clname, ClassPath.SYSTEM_CLASS_PATH);
  }

  /**
   * Handle one class read from disk.
   * @param clname the current class to handle
   * @param pathname the path where to find the specified class
   * @throws ClassNotFoundException if the class specified cannot be found
   * @throws IOException if the class executor has a writing problem
   */
  public void handleDiskClass(final String clname, 
                               final String pathname) throws ClassNotFoundException, 
                                                             IOException {
    final ClassPath cp = new ClassPath(pathname);
    System.out.println(cp);
    handleClass(clname, cp);

  }

  /**
   * Handle one class. The class name must be valid, and  the class
   * should be available in the class path.
   * @param clname the name of the class to load
   * @param cp the class path where to find the class
   * @throws ClassNotFoundException if the class is unavailable or if there
   * are some type resolution problems 
   * @throws IOException if the class executor has a writing problem
   */
  public void handleClass(final String clname, 
                           final ClassPath cp) throws ClassNotFoundException, IOException {
    final JavaClass jc = SyntheticRepository.getInstance(cp).loadClass(clname);
    fRepos.storeClass(jc);
    final ClassGen cg = new ClassGen(jc);
    String pn = jc.getPackageName();
    int packageName = fDico.getCoqPackageName(jc.getPackageName());
    if (packageName == 0) {
      packageName = fCurrentPackage++;
      fDico.addPackage(pn, packageName);
    }
    pn = Util.getCoqPackageName(pn);
    final String moduleName = Util.coqify(jc.getClassName());
    if (jc.isInterface()) {
      fTreatedInterfaces.add(moduleName + ".interface"); 
    } 
    else {
      fTreatedClasses.add(moduleName + ".class");
    }
    
    final ClassExecutor ce = new ClassExecutor(this, cg, fWorkingDir);
    ce.start();
    Util.writeln(fOut, 1, "Load \"" + ce.getOuputFile().getPath() + "\".");
  }

  
 
 

  /**
   * Write the file preable.
   */
  private void doBeginning() {
    Util.writeln(fOut, 0, fImplemSpecif.getBeginning());

    for (int i = 0; i < fSpecialLibs.length; i++) {
      final String str = fImplemSpecif.requireLib(Util.coqify(fSpecialLibs[i]));
      Util.writeln(fOut, 0, str);
      // out.newLine();
    }

    initDico(fDico);


    Util.writeln(fOut, 0, "Import P.");
    fOut.println();
    Util.writeln(fOut, 0, "Module TheProgram.");
    fOut.println();

  }

  /**
   * Initialize a dictionary with some standard values.
   * @param dico the dictionary to initialize
   */
  public static void initDico(final Dictionary dico) {
    final int javaLangPkg = 1;
    final int emptyPkg = 2;
    
    final int objClss = 1;
    final int objMeth = 12;
    
    final int thrwClss = 8;
    final int thrwMeth = 11;
    
    final int excpClss = 9;
    final int excpMeth = 10;
    
    final int strClss = 10;
    final int strMeth = 13;
    
    dico.addPackage("java/lang/", javaLangPkg);
    dico.addPackage("", emptyPkg);

    dico.addClass("Object", javaLangPkg, objClss);
    dico.addClass("Throwable", javaLangPkg, thrwClss);
    dico.addClass("Exception", javaLangPkg, excpClss);
    dico.addClass("String", javaLangPkg, strClss);
    
    dico.addMethod("Object.<init>", javaLangPkg, objClss, objMeth);
    dico.addMethod("Exception.<init>", javaLangPkg, excpClss, excpMeth);
    dico.addMethod("String.<init>", javaLangPkg, strClss, strMeth);
    dico.addMethod("Throwable.<init>", javaLangPkg, thrwClss, thrwMeth);
    // TODO complete the list...
  }

  /**
   * Write the file ending.
   */
  private void doEnding() {

    defineClassAndInterface();
    
    // the program definition
    Util.writeln(fOut, 1, "Definition program : Program := PROG.Build_t");
    Util.writeln(fOut, 2, "AllClasses");
    Util.writeln(fOut, 2, "AllInterfaces");
    Util.writeln(fOut, 1, ".");
    fOut.println();
    Util.writeln(fOut, 0, "End TheProgram.");
    fOut.println();
  }

  /**
   * Define all classes and interfaces.
   * @throws IOException
   */
  private void defineClassAndInterface() {
    // all classes
    String str = "Definition AllClasses : " + fImplemSpecif.classType() + " := ";
    for (String clss: fTreatedClasses) {
      str += fImplemSpecif.classCons(clss);
    }
    for (int i = 0; i < fSpecialLibs.length; i++) {
      str += fImplemSpecif.classCons(Util.coqify(fSpecialLibs[i]) + ".class");
    }
    str += " " + fImplemSpecif.classEnd() + ".";
    Util.writeln(fOut, 1, str);
    fOut.println();


    // all interfaces
    str = "Definition AllInterfaces : " + fImplemSpecif.interfaceType() + " := ";
    for (String interf: fTreatedInterfaces) {
      str += fImplemSpecif.interfaceCons(interf);
    }
    str += " " + fImplemSpecif.interfaceEnd() + ".";
    Util.writeln(fOut, 1, str);
    fOut.println();
  }



}
