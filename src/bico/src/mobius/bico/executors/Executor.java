package mobius.bico.executors;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import mobius.bico.MakefileGenerator;
import mobius.bico.Util;
import mobius.bico.Util.Stream;
import mobius.bico.dico.CamlDictionary;
import mobius.bico.dico.Dico;
import mobius.bico.dico.MethodHandler;
import mobius.bico.implem.IImplemSpecifics;
import mobius.bico.implem.ListImplemSpecif;
import mobius.bico.implem.MapImplemSpecif;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.util.ClassLoaderRepository;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;


/**
 * The main entry point to bico.
 * @author J. Charles (julien.charles@inria.fr), 
 * P. Czarnik (czarnik@mimuw.edu.pl), 
 * L. Hubert (laurent.hubert@irisa.fr)
 */
public class Executor extends ABasicExecutor {

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

  /** the coq files extension. */
  private static final String suffix = ".v";

  /** the standard lib paths. */
  //FIXME: should be relative to the package dir
  private static final String libPath = 
                      "Add LoadPath \"Formalisation/Library\".\n" + 
                      "Add LoadPath \"Formalisation/Library/Map\".\n" +
                      "Add LoadPath \"Formalisation/Bicolano\".\n";
  
  /** the name of the output file. */
  private File fFileName;

  /** classes to be parsed from standard library. */
  private final List<String> fOtherLibs = new ArrayList<String>();

  /** classes to be read from hand-made files. */
  private final String[] fSpecialLibs = {"java.lang.Object", "java.lang.Throwable",
                                         "java.lang.Exception", "java.lang.String" };

  /** list of already treated classes. */
  private List<ClassExecutor> fTreatedClasses = new ArrayList<ClassExecutor>();
  
  /** list of already treated interfaces. */
  private List<ClassExecutor> fTreatedInterfaces = new ArrayList<ClassExecutor>();
  
  /** tells whether or not the help message must be shown. */
  private boolean fShowHelp;

  
  /** the name of the executor file which will be declined to Type and Sig. */
  private String fName;
  
  /**
   * Minimal constructor.
   */
  private Executor() {
    super(new ClassLoaderRepository(ClassLoader.getSystemClassLoader()), new MapImplemSpecif(),
          new MethodHandler(), null, new CamlDictionary(), null);
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
   * A class loader that changes the behaviour of the loadClass method.
   * @author J. Charles (julien.charles@inria.fr)
   */
  private static class MyClassLoader extends ClassLoader {
    /**
     * Does a call to {@link #loadClass(String, boolean)}, but with the second
     * argument as true: the class has to be resolved.
     * @param name the name of the class to load
     * @return the newly loaded class
     * @throws ClassNotFoundException if the class cannot be retrieved
     */
    @Override
    public Class< ? > loadClass(final String name) throws ClassNotFoundException {
      return loadClass(name, true);
    }
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
    setBaseDir(workingDir);
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
    setBaseDir(pathname); 
    if (!pathname.isDirectory()) {
      setBaseDir(pathname.getParentFile());
    }
    fName = fImplemSpecif.getFileName(Util.coqify(pathname.getName()));
     

    fFileName = new File(getBaseDir(), fName + ".v");
    System.out.println("Output file: " + fFileName);
  }

  /**
   * Launch bico !
   * 
   * @throws IOException in case of any I/O errors....
   * @throws ClassNotFoundException if libraries 
   * file specified in {@link #fOtherLibs} cannot be found
   */
  public void start() throws ClassNotFoundException, IOException {
    if (fShowHelp) {
      System.out.println(HELP_MSG);
    }
    Dico.initDico(fDico);
    System.out.println("Using " + fImplemSpecif + ".");
    System.out.println("Working path: " + getBaseDir());
    // creating file for output
    if (fFileName.exists()) {
      fFileName.delete();
      System.out.println("previous file is being overwritten...");
    }
    fFileName.createNewFile();
    final FileOutputStream fwr = new FileOutputStream(fFileName);
    fOut = new Util.Stream(fwr);

    doMain();

    fOut.close(); // closing output file
    doType();
    doSignature();
    writeDictionnary();
  }

  /**
   * Write the main file.
   * @throws ClassNotFoundException if there is a problem with
   * name resolution
   * @throws IOException if there is a problem writing from the disk
   */
  private void doMain() throws ClassNotFoundException, IOException {
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
    
    generateMakefile();
  }

  /**
   * Generates the makefile to compile everything.
   */
  private void generateMakefile() {
    final List<ClassExecutor> treated = new ArrayList<ClassExecutor>();
    treated.addAll(fTreatedClasses);
    treated.addAll(fTreatedInterfaces);
    new MakefileGenerator(getBaseDir(), fName, treated).generate();
  }

  /**
   * Write the signature file.
   * @throws FileNotFoundException in case the file cannot be
   * written
   */
  private void doSignature() throws FileNotFoundException {
    final File typ = new File(getBaseDir(), fName + "_signature" + suffix);
    final Stream out = new Stream(new FileOutputStream(typ));
    out.println(libPath);
    out.println(fImplemSpecif.getBeginning());

    //out.println("Require Import " + fName + "_type.");
    out.println();
    out.incPrintln("Module " + fName + "Signature.");


    // the already treated classes + interfaces
    for (ClassExecutor ce: fTreatedClasses) {
      out.println("Load \"" + ce.getModuleFileName() + "_signature.v\".");
    }
    
    for (ClassExecutor ce: fTreatedInterfaces) {
      out.println("Load \"" + ce.getModuleFileName() + "_signature.v\".");
    }
    
    out.decPrintln("End " + fName + "Signature.");
    
  }

  /**
   * Write the type file.
   * @throws FileNotFoundException if the type file cannot be 
   * created
   */
  private void doType() throws FileNotFoundException {
    final File typ = new File(getBaseDir(), fName + "_type" + suffix);
    final Stream out = new Stream(new FileOutputStream(typ));
    out.println(libPath);
    out.println(fImplemSpecif.getBeginning());


    out.println();
    out.incPrintln("Module " + fName + "Type.");
    // the special library
    for (int i = 0; i < fSpecialLibs.length; i++) {
      final String str = fImplemSpecif.requireLib(Util.coqify(fSpecialLibs[i]));
      out.println("Load \"" + str + ".v\".");
    }
    

    // the already treated classes + interfaces
    for (ClassExecutor ce: fTreatedClasses) {
      out.println("Load \"" + ce.getModuleFileName() + "_type.v\".");
    }
    
    for (ClassExecutor ce: fTreatedInterfaces) {
      out.println("Load \"" + ce.getModuleFileName() + "_type.v\".");
    }
    
    out.decPrintln("End " + fName + "Type.");
  }

  /**
   * Write the dictionnary to a file.
   * @throws FileNotFoundException If there is a problem 
   * in writing.
   */
  private void writeDictionnary() throws FileNotFoundException {
    final File dicoFile = new File(getBaseDir(), "dico.ml");
    fOut = new Util.Stream(new FileOutputStream(dicoFile));
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
   * Handle one class from library files.
   * @param clname the class to load from the classpath
   * @throws ClassNotFoundException if the specified class cannot be found
   * @throws IOException if the class executor has a writing problem
   */
  public void handleLibraryClass(final String clname) throws ClassNotFoundException, 
                                                             IOException {
    final MyClassLoader mcl = new MyClassLoader(); 
    mcl.loadClass(clname);
    final ClassLoaderRepository rep = new ClassLoaderRepository(mcl); 
    handleClass(rep.loadClass(clname));
    
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
    //System.out.println(cp);
    handleClass(SyntheticRepository.getInstance(cp).loadClass(clname));

  }

  /**
   * Handle one class. The class name must be valid, and  the class
   * should be available in the class path.
   * @param jc the class to load
   * @throws ClassNotFoundException if the class is unavailable or if there
   * are some type resolution problems 
   * @throws IOException if the class executor has a writing problem
   */
  public void handleClass(final JavaClass jc) throws ClassNotFoundException, IOException {
    
    fRepos.storeClass(jc);
    final ClassGen cg = new ClassGen(jc);
    String pn = jc.getPackageName();
    
    pn = Util.getCoqPackageName(pn);
    final ClassExecutor ce = getClassExecutor(cg);
    
    if (jc.isInterface()) {
      fTreatedInterfaces.add(ce); 
    } 
    else {
      fTreatedClasses.add(ce);
    }
    fOut.println("Load \"" + ce.getModuleFileName() + ".v\".");
    
    ce.start();
  }
 
  /**
   * Returns an instance of a class executor.
   * This method is there as an extension point.
   * @param cg the class generator. Represents the current class
   * to treat.
   * @return a ClassExecutor instance
   * @throws FileNotFoundException if a file is missing
   */
  public ClassExecutor getClassExecutor(final ClassGen cg) throws FileNotFoundException {
    return new ClassExecutor(this, cg, fName);
  }

  /**
   * Write the file preable.
   */
  private void doBeginning() {
    fOut.println(libPath);
    fOut.println(fImplemSpecif.getBeginning());
    fOut.println("Require Import " + fName + "_type.");
    fOut.println("Require Import " + fName + "_signature.");


    fOut.println("Import P.\n");
    fOut.println("Import " + fName + "Type.");
    fOut.println("Import " + fName + "Signature.");
    fOut.incPrintln("Module " + fName + "Program.");

  }


  /**
   * Write the file ending.
   */
  private void doEnding() {

    defineClassAndInterface();
    
    // the program definition
    fOut.incPrintln("Definition program : Program := PROG.Build_t");
    fOut.println("AllClasses");
    fOut.println("AllInterfaces");
    fOut.decPrintln(".\n");
    fOut.decPrintln("End " + fName + "Program.\n");
  }

  /**
   * Define all classes and interfaces.
   * @throws IOException
   */
  private void defineClassAndInterface() {
    // all classes
    String str = "Definition AllClasses : " + fImplemSpecif.classType() + " := ";
    for (ClassExecutor clss: fTreatedClasses) {
      str += fImplemSpecif.classCons(clss.getModuleName() + ".class");
    }
    for (int i = 0; i < fSpecialLibs.length; i++) {
      str += fImplemSpecif.classCons(Util.coqify(fSpecialLibs[i]) + ".class");
    }
    str += " " + fImplemSpecif.classEnd() + ".";
    fOut.println(1, str);
    fOut.println();


    // all interfaces
    str = "Definition AllInterfaces : " + fImplemSpecif.interfaceType() + " := ";
    for (ClassExecutor interf: fTreatedInterfaces) {
      str += fImplemSpecif.interfaceCons(interf.getModuleName() + ".interface");
    }
    str += " " + fImplemSpecif.interfaceEnd() + ".";
    fOut.println(1, str);
    fOut.println();
  }
  
  /**
   * Returns the name of the module.
   * @return not null
   */
  public String getModuleName() {  
    return fName;
  }
}
