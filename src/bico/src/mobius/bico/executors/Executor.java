package mobius.bico.executors;

import java.io.File;
import java.io.FileFilter;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import mobius.bico.Util;
import mobius.bico.Util.Stream;
import mobius.bico.dico.CamlDictionary;
import mobius.bico.dico.Dico;
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
   * and operational semantics.
   */
  public static final String pathToLib = "";
  
  
  /**
   * Path "en dur" to the Mobius coq formalisation of a Java bytecode logic
   * and operational semantics.
   */
  public static final String pathToAPI = ""; //pathToLib //+ //"Formalisation" +File.separatorChar+ "java";
  
  
  /** the standard lib paths. */
  public static final String libPath = 
  	"Add LoadPath \"" + pathToLib + "Formalisation/Library\".\n" + 
  	"Add LoadPath \"" + pathToLib + "Formalisation/Library/Map\".\n" + 
  	"Add LoadPath \"" + pathToLib + "Formalisation/Logic\".\n" + 
  	"Add LoadPath \"" + pathToLib + "Formalisation/Bicolano\".\n" + 
  	"Add LoadPath \"" + pathToLib + pathToAPI + "\".\n";
  
//  /** the name of the output file. */
//  private File fCoqFileName;
  
  /** classes already parsed. */
  private final Map<String, ClassExecutor> fTreatedClasses = 
    new HashMap<String, ClassExecutor>();
  
  /** classes that are left to be treated. */
  private final List<String> fPendingClasses = 
    new ArrayList<String>();
  
  /** classes to be read from hand-made files. */
  private final String[] fSpecialLibs = { 
    "java.lang.Object",
    "java.lang.Throwable", 
    "java.lang.Exception", 
    "java.lang.String",
    "java.lang.NullPointerException",
    "java.util.LinkedList"
  };
  

  
  /** the name of the executor file which will be declined to Type and Sig. */
  private String fName;

  
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
  
  
  /**
   * Minimal constructor.
   * The copy constructor.
   * @param e the executor to create a copy from
   */
  public Executor(final Executor e) {
    super((ABasicExecutor) e);
    fName = e.fName;
    fPendingClasses.addAll(e.fPendingClasses);
  }
  

  
  
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

    if (classToTreat != null) {
      fPendingClasses.addAll(classToTreat);
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
  
 
  
  
  /**
   * Treat all classes in the directory passed as value to the 
   * input parameter <code>-lib</code>.
   * 
   * @throws IOException
   * @throws ClassNotFoundException
   */
  private void doApplication() throws ClassNotFoundException, IOException {
    collectClasses("");
    System.out.println("There are " + fPendingClasses.size() + " classe(s) pending.");
    while (!fPendingClasses.isEmpty()) {
      handleClass(fPendingClasses.get(0));
      fPendingClasses.remove(0);
    }
  
  }
  
  /**
   * Treat all classes in the directory passed as value to the 
   * input parameter <code>-lib</code>.
   * 
   * @param pkg the current package name
   * @throws IOException
   * @throws ClassNotFoundException
   */
  private void collectClasses(final String pkg) 
        throws ClassNotFoundException, IOException {
    final File baseDir = getBaseDir();
    final File f = new File(baseDir, pkg);
    final File[] classfiles = f.listFiles(new FileFilter() {
      public boolean accept(final File cf) {
        return ((cf.isFile()) && cf.getName().endsWith(Constants.CLASS_SUFFIX));
      }
    });
    
    final File[] dirfiles = f.listFiles(new Util.DirectoryFilter());
    
    System.out.println("Entering directory " + f + ".");
    System.out.println("Found " + classfiles.length + " classes.");
    for (File cf: classfiles) {
      String className = 
        pkg + Util.removeClassSuffix(cf.getName()); 
      className = className.replace(Constants.LINUX_PATH_SEPARATOR,
                                    Constants.JAVA_NAME_SEPARATOR);
      fPendingClasses.add(className);
    }
    
    for (File cf: dirfiles) {
      
      final String p = pkg + cf.getName() + 
                       Constants.PATH_SEPARATOR;
      // else handle the next package which is in the current
      // directory
      
      collectClasses(p);
      
     
    }
    //new MakefileGenerator(getBaseDir(), pkg, ).generate();
    System.out.println("Leaving directory " + f + ".");
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
    Dico.initDico(getDico());
    System.out.println("Using fImplemSpecif: " + getImplemSpecif() + ".");
    System.out.println("Working path: " + getBaseDir());
    
    doApplication();
    /*
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
    writeDictionnary();
    */
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
    
//    Iterator<ExternalClass> iter = fExtLibs.values().iterator();
//    while (iter.hasNext()) {
//    	ExternalClass current = iter.next();
//    	out.println(Constants.LOAD + Constants.SPACE + "\""
//    			+ current.getSignatureName() + "\".");
//    }
    
    // the already treated classes + interfaces
    for (Entry<String, ClassExecutor> ce : 
           fTreatedClasses.entrySet()) {
    	out.println(Constants.LOAD + " \"" + ce.getValue().getModuleFileName() + "_signature.v\".");
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
    
//    Iterator<ExternalClass> iter = fExtLibs.values().iterator();
//    while (iter.hasNext()) {
//    	ExternalClass current = iter.next();
//    	out.println(Constants.LOAD + Constants.SPACE + "\""
//    		+ current.getTypeName() + "\".");
//    }
    
    // the special library
    for (int i = 0; i < fSpecialLibs.length; i++) {
    	final String str = getImplemSpecif().requireLib(Util
    			.coqify(fSpecialLibs[i]));
    	out.println(Constants.LOAD + Constants.SPACE + "\"" + str
    				+ ".v\".");
    }
    
    // the already treated classes + interfaces
    for (Entry<String, ClassExecutor> ce : fTreatedClasses.entrySet()) {
      out.println(Constants.LOAD + " \"" + 
                  ce.getValue() + "_type.v\".");
    }
    
    out.decPrintln(Constants.END_MODULE + " " + 
                   fName + "Type.");
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
   * Tells if 
   * @param clname
   * @return
   */
  public boolean isSpecialLib(String clname) {
    for (String lib: fSpecialLibs) {
      if (lib.equals(clname)) {
        return true;
      }
    }
    return false;
  }


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
  public ClassExecutor handleClass(final String clname)
      throws ClassNotFoundException, IOException {
    if (clname == null) {
      return null;
    }
    if (isSpecialLib(clname) ||
        fTreatedClasses.containsKey(clname)) {
      return null;
    }
    return handleClass(getRepository().loadClass(clname));
  
  }
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
    final ClassGen cg = new ClassGen(jc);
    String pn = jc.getPackageName();
    pn = Util.getCoqPackageName(pn);
    final ClassExecutor ce = getClassExecutor(cg);
    fTreatedClasses.put(jc.getClassName(), ce);
    ce.start();
    final List<String> l = ce.getClassDependencies();
    System.out.println(l);
    for (String clzz: l) {
      if (!isSpecialLib(clzz) && !fTreatedClasses.containsKey(clzz)) {
        fPendingClasses.add(clzz);
      }
    }
    System.out.println();
    return ce;
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
    final List<ClassExecutor> treatedInterfaces = new ArrayList<ClassExecutor>();
    final List<ClassExecutor> treatedClasses = new ArrayList<ClassExecutor>();
  
    for (ClassExecutor ce: fTreatedClasses.values()) {
      if (ce.getJavaClass().isInterface()) {
        treatedInterfaces .add(ce);
      } 
      else {
        treatedClasses.add(ce);
      }
    }
    // all classes
    String str = Constants.DEFINITION + Constants.SPACE + "AllClasses : "
    		+ implem.classType() + " := ";
    for (ClassExecutor clss : treatedClasses) {
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
    for (ClassExecutor interf : treatedInterfaces) {
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
  
  
}
