package mobius.bico.executors;

import java.io.File;
import java.io.FileFilter;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import mobius.bico.Util;
import mobius.bico.coq.CoqStream;
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

  /** the coq files extension (.v). */
  public static final String suffix = ".v";
  
   
  /** the standard lib paths. */
  public static final String libPath = 
    "Add LoadPath \"Formalisation/Library\".\n" + 
    "Add LoadPath \"Formalisation/Library/Map\".\n" + 
    "Add LoadPath \"Formalisation/Logic\".\n" + 
    "Add LoadPath \"Formalisation/Bicolano\".\n"; 
    
  
  
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
    "java.lang.NullPointerException",
  };
  

  
  /** the name of the executor file which will be declined to Type and Sig. */
  private final String fName;

  
  /**
   * Minimal constructor.
   * 
   * @deprecated do not use, use a proper constructor instead
   */
  private Executor() {  
    super(new ClassLoaderRepository(ClassLoader.getSystemClassLoader()),
          new MapImplemSpecif(), new MethodHandler(), null,
          new CamlDictionary(), new File(""));
    fName = "Bico";
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
    fName = "Bico";
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
  public void doApplication() throws ClassNotFoundException, IOException {
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
    
    generateClassMakefiles();
    

    writeDictionnary();
    File fCoqFileName = new File(getBaseDir(), fName + suffix);
    // creating file for output
    if (fCoqFileName.exists()) {
      fCoqFileName.delete();
      System.out.println("previous file is being overwritten...");
    }
    fCoqFileName.createNewFile();
    final FileOutputStream fwr = new FileOutputStream(fCoqFileName);
    setOut(new CoqStream(fwr));
    doType();
    doSignature();
    doMain();
    generateMainMakefile();
    getOut().close(); // closing output file

  }
  
  /**
   * Write the main file. This generates for instance the file "B_classMap.v",
   * i.e. packageName_className.v
   * 
   * @throws ClassNotFoundException
   *             if there is a problem with name resolution
   * @throws IOException
   *             if there is a problem writing from the disk
   */
  private void doMain() throws ClassNotFoundException, IOException {
    // write prelude ;)
    final CoqStream out = getOut();
    printLoadPath(out);
    out.println(getImplemSpecif().getBeginning());
    out.println("Require Import ImplemSWp.");
    out.println("Import P.");
    out.println("Import MDom.\n");
    
    out.reqExport(fName + "_type");
    out.reqExport(fName + "_signature");
    
    out.exprt(fName + "Type");
    out.exprt(fName + "Signature");
    out.startModule(fName + "Program");
    // the special library
    for (int i = 0; i < fSpecialLibs.length; i++) {
      final String str = getImplemSpecif().requireLib(Util.coqify(fSpecialLibs[i]));
      out.load(str + ".v");
    }
    out.println();
    // the already treated classes + interfaces
    for (Entry<String, ClassExecutor> ce : fTreatedClasses.entrySet()) {
      out.load(ce.getValue().getModuleName() + ".v");
    }
    
    defineClassAndInterface();
    
    // the program definition
    out.incPrintln("Definition program : Program := PROG.Build_t");
    out.println("AllClasses");
    out.println("AllInterfaces");
    out.decPrintln(".\n");
    out.incPrintln("Definition subclass :=");
    out.println("match P.subclass_test program with\n" + 
                "| Some f => f\n" + 
                "| None => fun x y => true\n" +
                "end");
    out.decPrintln(".\n");
    out.endModule(fName + "Program");
  }



  
  public void generateMainMakefile() {
    
    final MakefileGen mg = new MakefileGen(getBaseDir());
    mg.generate();
  }
  
  public void generateClassMakefiles() {
    final ClassesMakefileGen cmg = new ClassesMakefileGen(getBaseDir(), 
                                                          fTreatedClasses.values());
    cmg.generate();
  }


  /**
   * Write the signature file.
   * 
   * @throws FileNotFoundException
   *             in case the file cannot be written
   */
  private void doSignature() throws FileNotFoundException {
    final File typ = new File(getBaseDir(), fName + "_signature" + suffix);
    /* final File typ = new File( fCoqName + "_signature" + suffix); */
    final CoqStream out = new CoqStream(new FileOutputStream(typ));
    printLoadPath(out);
    out.println(getImplemSpecif().getBeginning());
    
    out.println();
    out.incPrintln(Constants.MODULE + fName + "Signature.");
    
    // the special library
    for (int i = 0; i < fSpecialLibs.length; i++) {
      final String str = getImplemSpecif().requireLib(Util.coqify(fSpecialLibs[i]));
      out.load(str + ".v");
    }
    out.println();
    // the already treated classes + interfaces
    for (Entry<String, ClassExecutor> ce : 
           fTreatedClasses.entrySet()) {
      out.load(ce.getValue().getModuleName() + "_signature.v");
    }
    

    
    out.decPrintln(Constants.END_MODULE + fName + "Signature.");
  
  }
  
  /**
   * Write the type file.
   * 
   * @throws FileNotFoundException
   *             if the type file cannot be created
   */
  private void doType() throws FileNotFoundException {
    final File typ = new File(getBaseDir(), fName + "_type" + suffix);
    final CoqStream out = new CoqStream(new FileOutputStream(typ));

    printLoadPath(out);
    out.println(getImplemSpecif().getBeginning());
    
    out.println();
    out.incPrintln(Constants.MODULE + fName + "Type.");

    
    // the special library
    for (int i = 0; i < fSpecialLibs.length; i++) {
      final String str = getImplemSpecif().requireLib(Util.coqify(fSpecialLibs[i]));
      out.load(str + ".v");
    }
    out.println();
    // the already treated classes + interfaces
    for (Entry<String, ClassExecutor> ce : fTreatedClasses.entrySet()) {
      out.load(ce.getValue().getModuleName() + "_type.v");
    }
    
    out.decPrintln(Constants.END_MODULE + " " + 
                   fName + "Type.");
  }


  private void printLoadPath(final CoqStream out) {
    out.println(libPath);
    final Set<String> set = new HashSet<String>();
    for (Entry<String, ClassExecutor> ce : fTreatedClasses.entrySet()) {
      final String pkg = "classes/" + ce.getValue().getPackageDir().toString();
      set.add(pkg);
    }
    
    // the special library
    for (int i = 0; i < fSpecialLibs.length; i++) {
      final String str = getImplemSpecif().requireLib(Util.coqify(fSpecialLibs[i]));
      out.load(str + ".v");
    }
    out.println();
    
    for (String s: set) {
      out.println (Constants.ADD_LOAD_PATH + "\"" + s + "\".");
    }
  }
  
  /**
   * Write the dictionnary to a file.
   * 
   * @throws FileNotFoundException
   *             If there is a problem in writing.
   */
  private void writeDictionnary() throws FileNotFoundException {
    final File dicoFile = new File(getBaseDir(), "dico.ml");
    final CoqStream out = new CoqStream(new FileOutputStream(dicoFile));
    getDico().write(out);
    out.close();
  }

  

  
  /**
   * Tells if the given classname represents a special lib.
   * @param clname the class name to verify
   * @return true if nothing should be generated for it
   */
  public boolean isSpecialLib(final String clname) {
    if (clname.startsWith("java")) {
      return true;
    }
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
   * @return the newly created class executor for the given class or 
   * <code>null</code>
   */
  public ClassExecutor handleClass(final String clname) throws ClassNotFoundException, 
                                                               IOException {
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
   * @return the newly created class executor for the given class or 
   * <code>null</code>
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
   * Define all classes and interfaces.
   * 
   * @throws IOException
   */
  private void defineClassAndInterface() {
    final IImplemSpecifics implem = getImplemSpecif();
    final CoqStream ot = getOut();
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
    String str = Constants.DEFINITION + "AllClasses : " + implem.classType() + " := ";
    for (ClassExecutor clss : treatedClasses) {
      str += implem.classCons(clss.getModuleName() + ".class");
    }
    for (int i = 0; i < fSpecialLibs.length; i++) {
      str += implem.classCons(Util.coqify(fSpecialLibs[i]) + ".class");
    }
    str += " " + implem.classEnd() + ".";
    ot.println(1, str);
    ot.println();
    
    // all interfaces
    str = Constants.DEFINITION + "AllInterfaces : " + implem.interfaceType() + " := ";
    for (ClassExecutor interf : treatedInterfaces) {
      str += implem.interfaceCons(interf.getModuleName() + ".interface");
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
  
  
  public Collection<ClassExecutor> getTreatedClasses() {
    
    return fTreatedClasses.values();
  }
  
}
