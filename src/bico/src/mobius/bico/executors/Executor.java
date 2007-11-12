package mobius.bico.executors;

import java.io.File;
import java.io.FileFilter;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import mobius.bico.MakefileGenerator;
import mobius.bico.Util;
import mobius.bico.Util.Stream;
import mobius.bico.dico.CamlDictionary;
import mobius.bico.dico.MethodHandler;
import mobius.bico.implem.IImplemSpecifics;
import mobius.bico.implem.MapImplemSpecif;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.util.ClassLoaderRepository;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;

/**
 * The main entry point to bico.
 * 
 * @author J. Charles (julien.charles@inria.fr), P. Czarnik
 *         (czarnik@mimuw.edu.pl), L. Hubert (laurent.hubert@irisa.fr)
 */
public class Executor extends ABasicExecutor {

  /** the coq files extension. */
  public static final String suffix = ".v";
  
  /**
   * Path "en dur" to the Mobius coq formalisation of a Java bytecode logic
   * and operational semantics
   */
  public static final String pathToLib = "";
  
  
  /**
   * Path "en dur" to the Mobius coq formalisation of a Java bytecode logic
   * and operational semantics
   */
  public static final String pathToAPI = ""; //pathToLib //+ //"Formalisation" +File.separatorChar+ "java";
  
  
  /** the standard lib paths. */
  public static final String libPath = 
  	"Add LoadPath \"" + pathToLib + "Formalisation/Library\".\n" + 
  	"Add LoadPath \"" + pathToLib + "Formalisation/Library/Map\".\n" + 
  	"Add LoadPath \"" + pathToLib + "Formalisation/Logic\".\n" + 
  	"Add LoadPath \"" + pathToLib + "Formalisation/Bicolano\".\n" + 
  	"Add LoadPath \"" + pathToLib + pathToAPI + "\".\n";
  
  
  
  /** the name of the output file. */
  private File fCoqFileName;
  
  /** classes to be parsed from standard library. */
  protected static final HashMap<String, ExternalClass> fExtLibs = new HashMap<String, ExternalClass>();
  
  /** classes to be parsed from current library. */
  private static final HashMap<String, ClassExecutor> fCurrentLibs = new HashMap<String, ClassExecutor>();
  
  /** classes to be read from hand-made files. */
  private final String[] fSpecialLibs = { "java.lang.Object",
  		"java.lang.Throwable", "java.lang.Exception", "java.lang.String",
  		"java.lang.NullPointerException" };
  
  /** list of already treated classes. */
  private static final List<ClassExecutor> fTreatedClasses = new ArrayList<ClassExecutor>();
  
  /** list of already treated interfaces. */
  private static final List<ClassExecutor> fTreatedInterfaces = new ArrayList<ClassExecutor>();
  
//  /** tells whether or not the help message must be shown. */
//  private boolean fShowHelp;
//  
  
  /** the name of the executor file which will be declined to Type and Sig. */
  private String fName;
  

  
//  /**
//   * directory where are the classes referenced in the file to be compiled in
//   * bico.
//   */
  //File fLibDir;
  

  
  //private File fExtDir;
  
  /**
   * Minimal constructor.
   * 
   * @deprecated do not use, use a proper constructor instead
   */
  private Executor() {  
  	super(new ClassLoaderRepository(ClassLoader.getSystemClassLoader()),
          new MapImplemSpecif(), new MethodHandler(), null,
          new CamlDictionary(), new File(""));
  }
  
//  /**
//   * Parses the arguments given in the parameter. Each argument is in one cell
//   * of the array, as in a {@link #main(String[])} method. Mainly initialize
//   * all the private variables from <code>Executor</code>
//   * 
//   * @param args
//   *            The argument given to <tt>bico</tt>
//   */
//  public Executor(final String[] args) {
//    this();
//    // initialise the arguments. In particular, the path fBaseDir to the
//    // class files will be set properly
//    init(args);
//    final String clPath = getBaseDir().getAbsolutePath().toString() + 
//                          File.pathSeparatorChar + ClassPath.getClassPath();
//    System.out.println("Class Path " + clPath);
//    // set the Repository to be a synthetic repository
//    setRepository(SyntheticRepository.getInstance(new ClassPath(clPath)));
//  }
  
  
  /**
   * Minimal constructor.
   * The copy constructor.
   * @param e the executor to create a copy from
   */
  public Executor(final Executor e) {
    super((ABasicExecutor) e);
  }
  
  
  /**
   * Treat all classes in the directory passed as value to the 
   * input parameter <code>-lib</code>.
   * 
   * @throws IOException
   * @throws ClassNotFoundException
   */
  private void doApplication() throws ClassNotFoundException, IOException {
    doApplication("");
  
  }
  
  /**
   * Treat all classes in the directory passed as value to the 
   * input parameter <code>-lib</code>.
   * 
   * @param pkg the current package name
   * @throws IOException
   * @throws ClassNotFoundException
   */
  private void doApplication(final String pkg) 
        throws ClassNotFoundException, IOException {
    final File baseDir = getBaseDir();
    final File f = new File(baseDir, pkg);
    final File[] classfiles = f.listFiles(new FileFilter() {
      public boolean accept(final File cf) {
        return ((cf.isFile()) && cf.getName().endsWith(Constants.CLASS_SUFFIX));
      }
    });
    
    final File[] dirfiles = f.listFiles(new FileFilter() {
      public boolean accept(final File cf) {
        System.out.println(cf);
        return cf.isDirectory() && !cf.getParent().equals(cf);
      }
    });
    if (classfiles == null) {
      return;
    }
   
    for (File cf: classfiles) {
      // if the file is a class file then
      // handle it
      String className = 
        pkg + Util.removeClassSuffix(cf.getName());        
      className =
        className.replace(Constants.LINUX_PATH_SEPARATOR,
                          Constants.JAVA_NAME_SEPARATOR);
      handleLibraryClass(className);
    }
    
    for (File cf: dirfiles) {
      final String p = pkg + cf.getName() + 
                       Constants.PATH_SEPARATOR;
      // else handle the next package which is in the current
      // directory
      
      doApplication(p);
      new MakefileGenerator(getBaseDir(), p).generate();
    }
  }
  
  /**
   * 
   * @param cl
   *            the JavaClass object to which the {@link #javaClass javaClass}
   *            field will be set to}
   */
  /*
   * protected void setJavaClass(JavaClass cl) { javaClass = cl; }
   */
  
  /*	*//**
  		 * the method adds the string representing a qualified class name in
  		 * the hashmap <code>fOtherLibs</code> if there is not already an
  		 * element with such a key. The method returns true if the method
  		 * parameter <code>clName</code> was added to
  		 * <code>fOtherLibs</code> and false otherwise
  		 * 
  		 * @param clName
  		 * @return
  		 */
  /*
   * public boolean addToOtherLibs(String clName) { if
   * (!fOtherLibs.containsKey(clName)) { fOtherLibs.put(clName, clName);
   * return true; } return false; }
   */
  
  /**
   * A class loader that changes the behaviour of the loadClass method.
   * 
   * @author J. Charles (julien.charles@inria.fr)
   */
  /*
   * private static class MyClassLoader extends ClassLoader {
   *//**
  	 * Does a call to {@link #loadClass(String, boolean)}, but with the
  	 * second argument as true: the class has to be resolved.
  	 * 
  	 * @param name
  	 *            the name of the class to load
  	 * @return the newly loaded class
  	 * @throws ClassNotFoundException
  	 *             if the class cannot be retrieved
  	 */
  /*
   * @Override public Class<?> loadClass(final String name) throws
   * ClassNotFoundException { return loadClass(name, true); } }
   */
  
  /**
   * Create a new Executor object.
   * 
   * @param implem specify the implementation to use
   * @param workingDir the current working dir
   * @param outputDir the output directory
   * @param clzzPath the classpath to use
   * @param classToTreat the list of classes to treat
   */
  public Executor(final IImplemSpecifics implem, 
                  final File workingDir,
                  final File outputDir, 
                  final ClassPath clzzPath,
                  final List<String> classToTreat) {
    super(SyntheticRepository.getInstance(clzzPath),
          implem, 
          new MethodHandler(), 
          null,
          new CamlDictionary(), 
          workingDir);
    
    
    // if the list of other classes to treat is empty exit from the
    // constructor
    if (classToTreat != null) {
      for (String clName: classToTreat) { 
        //addToOtherLibs(clName); 
      }
    }
  }
  /**
   * Create a new Executor object.
   * 
   * @param implem specify the implementation to use
   * @param workingDir the current working dir
   * @param outputDir the output directory
   * @param classToTreat the list of classes to treat
   */
  public Executor(final IImplemSpecifics implem, 
                  final File workingDir,
                  final File outputDir, 
                  final List<String> classToTreat) {
    this(implem, 
         workingDir, 
         outputDir,
         new ClassPath(workingDir.getAbsolutePath() + 
                       File.pathSeparatorChar + ClassPath.getClassPath()),
         classToTreat);
  }
  
 
  
  private void setExtDir(File f) {
  	//fExtDir = f;
  }
  
  private void initFName(String _fname) {
  	//fName = _fname;
  }
  
  /**
   * initialises the file base file name in which the bicolano version of the
   * class file will be stored
   * 
   * @param _fName
   */
  private void initWorkingFile(String _fName) {
  	fName = getImplemSpecif().getFileName(Util.coqify(_fName));
  }
  
  /**
   * initialises the file path including the file where the bico fName will be
   * stored
   */
  private void initCoqFName() {
    fCoqFileName = new File(getBaseDir(), fName + ".v");
    System.out.println("Output file: " + fCoqFileName);
  }
  
  
  
  /**
   * Launch bico !
   * 
   * @throws IOException
   *             in case of any I/O errors....
   * @throws ClassNotFoundException
   *             if libraries file specified in {@link #fExtLibs} cannot be
   *             found
   */
  public void start() throws ClassNotFoundException, IOException {
  	doApplication();
  	/*
  	if (fShowHelp) {
  		
  	}
  	Dico.initDico(fDico);
  	System.out.println("Using fImplemSpecif: " + fImplemSpecif + ".");
  	System.out.println("Working path: " + getBaseDir());
  	// creating file for output
  	if (fCoqFileName.exists()) {
  		fCoqFileName.delete();
  		System.out.println("previous file is being overwritten...");
  	}
  	fCoqFileName.createNewFile();
  	final FileOutputStream fwr = new FileOutputStream(fCoqFileName);
  	fOut = new Util.Stream(fwr);
  	
  	doMain();
  	
  	fOut.close(); // closing output file
  	doType();
  	doSignature();
  	writeDictionnary();*/
  }
  
  /*	*//**
   * Write the main file. This generates for instance the file "B_classMap.v",
   * i.e. packageName_className.v
   * 
   * @throws ClassNotFoundException
   *             if there is a problem with name resolution
   * @throws IOException
   *             if there is a problem writing from the disk
   *//*
  private void doMain() throws ClassNotFoundException, IOException {
  	// write prelude ;)
  	doBeginning();
  
  	// commented on 30/10
  	// handle library classes specified as 'the other libs'
  	
  	 * Iterator<String> iter = fOtherLibs.values().iterator(); while (
  	 * iter.hasNext()) { String current = iter.next();
  	 * System.out.println("Handling classes imported in the current class: " +
  	 * current); handleLibraryClass(current); }
  	 
  	doApplication();
  	addToTreated();
  	Iterator<ExternalClass> iter = fExtLibs.values().iterator();
  	fOut.println("(*Start of external librariess*)");
  	while (iter.hasNext()) {
  		ExternalClass current = iter.next();
  		fOut.println(Constants.LOAD + Constants.SPACE + "\""
  				+ current.getBicoClassName() + "\".");
  
  	}
  	fOut.println("(*End of xternal libraries DONE*)");
  	fOut.println("(*Start of libraries of the current application*)");
  	// the already treated classes + interfaces
  	for (ClassExecutor ce : fTreatedClasses) {
  		fOut.println(Constants.LOAD + Constants.SPACE + "\""
  				+ ce.getModuleFileName() + ".v\".");
  	}
  
  	for (ClassExecutor ce : fTreatedInterfaces) {
  		fOut.println(Constants.LOAD + Constants.SPACE + "\""
  				+ ce.getModuleFileName() + ".v\".");
  	}
  	fOut.println("(*End of current libs DONE*)");
  	doEnding();
  	generateMakefile();
  }*/
  
  /**
   * 
   *@deprecated
   */
  //commented by Mariela
  /**
   * Generates the makefile to compile everything.
   *//*
  private void generateMakefile() {
  	final List<ClassExecutor> treated = new ArrayList<ClassExecutor>();
  	treated.addAll(fTreatedClasses);
  	treated.addAll(fTreatedInterfaces);
  	getMakefileGenerator(getBaseDir(), fCoqName, treated).generate();
  }
  
  public MakefileGenerator getMakefileGenerator(final File file,
  		final String name, final List<ClassExecutor> treated) {
  	return new MakefileGenerator(file, name, treated);
  }*/
  
  /**
   * Write the signature file.
   * 
   * @throws FileNotFoundException
   *             in case the file cannot be written
   */
  private void doSignature() throws FileNotFoundException {
    final File typ = new File(getBaseDir(), fName + "_signature"
    		+ suffix);
    /* final File typ = new File( fCoqName + "_signature" + suffix); */
    final Stream out = new Stream(new FileOutputStream(typ));
    out.println(libPath);
    out.println(getImplemSpecif().getBeginning());
    
    // out.println("Require Import " + fName + "_type.");
    out.println();
    out.incPrintln(Constants.MODULE + Constants.SPACE + fName
    		+ "Signature.");
    
    Iterator<ExternalClass> iter = fExtLibs.values().iterator();
    while (iter.hasNext()) {
    	ExternalClass current = iter.next();
    	out.println(Constants.LOAD + Constants.SPACE + "\""
    			+ current.getSignatureName() + "\".");
    }
    
    // the already treated classes + interfaces
    for (ClassExecutor ce : fTreatedClasses) {
    	out.println(Constants.LOAD + Constants.SPACE + "\""
    			+ ce.getModuleFileName() + "_signature.v\".");
    }
    
    for (ClassExecutor ce : fTreatedInterfaces) {
    	out.println(Constants.LOAD + Constants.SPACE + "\""
    			+ ce.getModuleFileName() + "_signature.v\".");
    }
    
    out.decPrintln(Constants.END_MODULE + Constants.SPACE + fName
    		+ "Signature.");
  
  }
  
  /**
   * Write the type file.
   * 
   * @throws FileNotFoundException
   *             if the type file cannot be created
   */
  private void doType() throws FileNotFoundException {
    final File typ = new File(getBaseDir(), fName + "_type" + suffix);
    final Stream out = new Stream(new FileOutputStream(typ));
    out.println(libPath);
    out.println(getImplemSpecif().getBeginning());
    
    out.println();
    out.incPrintln(Constants.MODULE + Constants.SPACE + fName + "Type.");
    
    Iterator<ExternalClass> iter = fExtLibs.values().iterator();
    while (iter.hasNext()) {
    	ExternalClass current = iter.next();
    	out.println(Constants.LOAD + Constants.SPACE + "\""
    		+ current.getTypeName() + "\".");
    }
    
    // the special library
    for (int i = 0; i < fSpecialLibs.length; i++) {
    	final String str = getImplemSpecif().requireLib(Util
    			.coqify(fSpecialLibs[i]));
    	out.println(Constants.LOAD + Constants.SPACE + "\"" + str
    				+ ".v\".");
    }
    
    // the already treated classes + interfaces
    for (ClassExecutor ce : fTreatedClasses) {
    	out.println(Constants.LOAD + Constants.SPACE + "\""
    		+ ce.getModuleFileName() + "_type.v\".");
    }
    
    for (ClassExecutor ce : fTreatedInterfaces) {
    	out.println(Constants.LOAD + Constants.SPACE + "\""
    		+ ce.getModuleFileName() + "_type.v\".");
    }
    
    out.decPrintln(Constants.END_MODULE + Constants.SPACE + fName
    		+ "Type.");
  }
  
  /**
   * Write the dictionnary to a file.
   * 
   * @throws FileNotFoundException
   *             If there is a problem in writing.
   */
  private void writeDictionnary() throws FileNotFoundException {
    final File dicoFile = new File(getBaseDir(), "dico.ml");
    final Stream out = new Util.Stream(new FileOutputStream(dicoFile));
    getDico().write(out);
    out.close();
  }
  
  /**
   * Scan for classes in the current directory.
   * 
   * @return a list of class files found in the current directory
   */
  /*
   * private List<String> findFiles() { // FIXME: should not be needed final
   * List<String> files = new ArrayList<String>(); final File f =
   * fCoqFileName.getParentFile(); final String[] list = f.list();
   * 
   * for (String current : list) { if (current.endsWith(".class")) { final int
   * pom = current.indexOf("."); files.add(current.substring(0, pom)); } }
   * System.out.println("Found " + files.size() + " class file(s) in the
   * working path."); return files; }
   */
  
  /**
   * Handle one class from library files. The method "filters" classes which
   * are not in the current <code>fBaseDir</code> directory. By this, we
   * mean that if the class is not in the base directory, then we do not
   * compile it to bicolano. If the class is in the current base directory
   * then we proceed to its compilation
   * 
   * @param clname
   *            the class to load from the classpath
   * @throws ClassNotFoundException
   *             if the specified class cannot be found
   * @throws IOException
   *             if the class executor has a writing problem
   */
  public ClassExecutor handleLibraryClass(final String clname)
  		throws ClassNotFoundException, IOException {
    if (clname == null) {
      return null;
    }
    String c = clname;
    if (c.endsWith(Constants.CLASS_SUFFIX)) {
      c = Util.removeClassSuffix(c);
    }
    
    // if the class is already treated then return
    if (fCurrentLibs.get(c.replace('/', '.')) != null) {
      return null;
    }
    /*
     * final MyClassLoader mcl = new MyClassLoader(); mcl.loadClass(clname);
     * final ClassLoaderRepository rep = new ClassLoaderRepository(mcl);
     */
    return handleClass(getRepository().loadClass(c));
  
  }
  
  /**
   * Handle one class read from disk.
   * 
   * @param clname
   *            the current class to handle
   * @param pathname
   *            the path where to find the specified class
   * @throws ClassNotFoundException
   *             if the class specified cannot be found
   * @throws IOException
   *             if the class executor has a writing problem
   */
  /*
   * public void handleDiskClass(final String clname, final String pathname)
   * throws ClassNotFoundException, IOException { final ClassPath cp = new
   * ClassPath(pathname); // System.out.println(cp);
   * handleClass(SyntheticRepository.getInstance(cp).loadClass(clname)); }
   */
  
  /**
   * Handle one class. The class name must be valid, and the class should be
   * available in the class path.
   * 
   * @param jc
   *            the class to load
   * @throws ClassNotFoundException
   *             if the class is unavailable or if there are some type
   *             resolution problems
   * @throws IOException
   *             if the class executor has a writing problem
   */
  private ClassExecutor handleClass(final JavaClass jc) throws ClassNotFoundException,
  		IOException {
    // fRepos.storeClass(jc);
    final ClassGen cg = new ClassGen(jc);
    String pn = jc.getPackageName();
    pn = Util.getCoqPackageName(pn);
    final ClassExecutor ce = getClassExecutor(cg);
    fCurrentLibs.put(jc.getClassName(), ce);
    /* addToTreated(ce); */
    ce.start();
    return ce;
  }
  
  /*
   * public void addToTreated1(ClassExecutor ce) { if
   * (ce.getJavaClass().isInterface()) { fTreatedInterfaces.add(ce); } else {
   * fTreatedClasses.add(ce); } }
   */
  public void addToTreated() {
    
    for (ClassExecutor ce: fCurrentLibs.values()) {
      if (ce.getJavaClass().isInterface()) {
        fTreatedInterfaces.add(ce);
      } 
      else {
        fTreatedClasses.add(ce);
      }
    }
  }
  
  /**
   * Returns an instance of a class executor. This method is there as an
   * extension point.
   * 
   * @param cg
   *            the class generator. Represents the current class to treat.
   * @return a ClassExecutor instance
   * @throws FileNotFoundException
   *             if a file is missing
   */
  public ClassExecutor getClassExecutor(final ClassGen cg)
  		throws FileNotFoundException {
  	return new ClassExecutor(this, cg, fName);
  }
  
  /**
   * Write the file preable.
   */
  private void doBeginning() {
    final Stream out = getOut();
    out.println(libPath);
    out.println(getImplemSpecif().getBeginning());
    out.println("Require Import ImplemSWp.");
    out.println("Import P.");
    out.println("Import MDom.\n");
    
    out.println(Constants.REQ_EXPORT + Constants.SPACE + fName
    		+ "_type.");
    System.out.println(Constants.REQ_EXPORT + Constants.SPACE + fName
    		+ "_type.");
    out.println(Constants.REQ_EXPORT + Constants.SPACE + fName
    		+ "_signature.");
    
    out.println(Constants.EXPORT + Constants.SPACE + fName + "Type.");
    out.println(Constants.EXPORT + Constants.SPACE + fName
    		+ "Signature.");
    out.incPrintln(Constants.MODULE + Constants.SPACE + fName
    		+ "Program.");
  
  }
  
  /**
   * Write the file ending.
   */
  private void doEnding() {
    final Stream out = getOut();
    defineClassAndInterface();
    
    // the program definition
    out.incPrintln("Definition program : Program := PROG.Build_t");
    out.println("AllClasses");
    out.println("AllInterfaces");
    out.decPrintln(".\n");
    out.incPrintln("Definition subclass :=");
    out.println("match P.subclass_test program with\n" + "| Some f => f\n"
    		+ "| None => fun x y => true");
    out.println("end");
    out.decPrintln(".\n");
    out.decPrintln(Constants.END_DEFINITION + Constants.SPACE + fName
    		+ "Program.\n");
  }
  
  /**
   * Define all classes and interfaces.
   * 
   * @throws IOException
   */
  private void defineClassAndInterface() {
    final IImplemSpecifics implem = getImplemSpecif();
    final Stream ot = getOut();
    // all classes
    String str = Constants.DEFINITION + Constants.SPACE + "AllClasses : "
    		+ implem.classType() + " := ";
    for (ClassExecutor clss : fTreatedClasses) {
    	str += implem.classCons(clss.getModuleName() + ".class");
    }
    for (int i = 0; i < fSpecialLibs.length; i++) {
    	str += implem.classCons(Util.coqify(fSpecialLibs[i])
    			+ ".class");
    }
    str += " " + implem.classEnd() + ".";
    ot.println(1, str);
    ot.println();
    
    // all interfaces
    str = Constants.DEFINITION + Constants.SPACE + "AllInterfaces : "
    		+ implem.interfaceType() + " := ";
    for (ClassExecutor interf : fTreatedInterfaces) {
    	str += implem.interfaceCons(interf.getModuleName()
    			+ ".interface");
    }
    str += " " + implem.interfaceEnd() + ".";
    ot.println(1, str);
    ot.println();
  }
  
  /**
   * Returns the name of the module, the content of the field
   * {@link #fName}.
   * 
   * @return not null
   */
  public String getModuleName() {
    return fName;
  }
  
  /**
   * Return the list of the classes treated by the executor.
   * 
   * @return a list: can be empty.
   */
  public List<ClassExecutor> getTreatedClasses() {
    return fTreatedClasses;
  }
  
  /**
   * Return the list of the classes treated by the executor.
   * 
   * @return a list: can be empty.
   */
  public List<ClassExecutor> getTreatedInterfaces() {
    return fTreatedInterfaces;
  }
  
}
