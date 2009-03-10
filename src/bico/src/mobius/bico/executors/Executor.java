package mobius.bico.executors;

import java.io.File;
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
import java.util.Stack;
import java.util.Map.Entry;

import mobius.bico.Util;
import mobius.bico.bicolano.coq.CoqStream;
import mobius.bico.bicolano.coq.LoadPath;
import mobius.bico.dico.CamlDictionary;
import mobius.bico.dico.Dico;
import mobius.bico.dico.MethodHandler;
import mobius.bico.implem.IImplemSpecifics;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;



/**
 * The main entry point to bico.
 * 
 * @author J. Charles (julien.charles@inria.fr), P. Czarnik
 *         (czarnik@mimuw.edu.pl), L. Hubert (laurent.hubert@irisa.fr)
 */
public class Executor extends ABasicExecutor {

  /** the standard lib paths. */
  public static final String [] libPaths = {"Formalisation/Library",
                                            "Formalisation/Library/Map",
                                            "Formalisation/Bicolano",
                                            "Formalisation/Logic"};
  
  /** classes already parsed. */
  private final Map<String, ClassExecutor> fTreatedClasses = 
    new HashMap<String, ClassExecutor>();
  
  /** classes that are left to be treated. */
  private final Stack<String> fPendingClasses = 
    new Stack<String>();
  
  /** classes to be read from hand-made files. */
  private final String[] fSpecialLibs = { 
    "java.lang.Object",
    "java.lang.Throwable", 
    "java.lang.Exception", 
    "java.lang.NullPointerException",
  };
  
  /** true if the java libs are generated. */
  private boolean fGenerateJavaLibs; 

  /** the directory from which to collect the files to translate. */
  private final File fSourceDir;
  /** all the names associated with the executor file. */
  private final NamingData fNamingData;  
  
  /**
   * Minimal constructor.
   * The copy constructor.
   * @param e the executor to create a copy from
   */
  public Executor(final Executor e) {
    super(e);
    fSourceDir = e.fSourceDir;
    fPendingClasses.addAll(e.fPendingClasses);
    fNamingData = new NamingData(e.fNamingData);
    org.apache.bcel.Repository.setRepository(getRepository());
  }
  

  /**
   * Create a new Executor object.
   * 
   * @param li all the informations to launch the executor
   */
  public Executor(final LaunchInfos li) {
    this(li.fImplem, li.fBaseDir, li.fTargetDir, li.fClassPath,
         li.fClassToTreat, li.fGenerateLibs);
  }
  
  /**
   * Create a new Executor object.
   * 
   * @param implem specify the implementation to use
   * @param sourceDir the current working dir
   * @param outputDir the output directory
   * @param clzzPath the classpath to use
   * @param classToTreat the list of classes to treat
   * @param generateLibs whether or not the libraries shall
   * be generated
   */
  public Executor(final IImplemSpecifics implem, 
                  final File sourceDir,
                  final File outputDir, 
                  final ClassPath clzzPath,
                  final List<String> classToTreat,
                  final boolean generateLibs) {
    super(SyntheticRepository.getInstance(clzzPath),
          implem, 
          new MethodHandler(), 
          null,
          new CamlDictionary(), 
          outputDir);

    if (classToTreat != null) {
      fPendingClasses.addAll(classToTreat);
    }
    fSourceDir = sourceDir;

    fGenerateJavaLibs = generateLibs;
    fNamingData = new NamingData("Bico");
    org.apache.bcel.Repository.setRepository(getRepository());
  }

  
  /**
   * Treat all classes in the directory passed as value to the 
   * input parameter <code>-lib</code>.
   * @throws IOException if the output file cannot be written
   * @throws ClassNotFoundException if the main file or a dependency file cannot be found
   */
  public void doApplication() throws ClassNotFoundException, IOException {
    Util.collectClasses(fSourceDir, "");
    System.out.println("There are " + fPendingClasses.size() + " classe(s) pending.");
    while (!fPendingClasses.isEmpty()) {
      handleClass(fPendingClasses.pop());
    }
  
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
    System.out.println("Using implem: " + getImplemSpecif() + ".");
    final File base = getBaseDir();
    System.out.print("Source directory '" + fSourceDir + "':");    
    if (!checkCreated(fSourceDir)) {
      return; 
    }
    System.out.println(" OK.");
    System.out.print("Output directory '" + base + "':");    

    if (!checkCreated(base)) {
      return; 
    }
    System.out.println(" OK.");
    
    doApplication();
    
    generateClassMakefiles();

    final File fCoqFileName = new File(base, fNamingData.getBicoClassFileName());
    // creating file for output
    if (fCoqFileName.exists()) {
      fCoqFileName.delete();
      System.out.println("Previous file is being overwritten...");
    }
    fCoqFileName.createNewFile();
    final FileOutputStream fwr = new FileOutputStream(fCoqFileName);
    setOut(new CoqStream(fwr));
    doType();
    doSignature();
    doMain();
    generateMainMakefile();
    getOut().close(); // closing output file
    System.out.println("done.");

  }


  private boolean checkCreated(final File dir) {
    if (!dir.exists() &&
        !dir.mkdirs()) {
      System.err.println(" the directory does not exist and I failed to create it!");
      return false;
    }
    return true;
  }
  
  /**
   * Write the main file. This generates for instance the file "B_classMap.v",
   * i.e. packageName_className.v
   */
  private void doMain() {

    final CoqStream out = getOut();
    
    printMainPrelude(out);
    
    out.startModule(fNamingData.getModuleName() + "Program");
    // the special library
    for (int i = 0; (!fGenerateJavaLibs) && (i < fSpecialLibs.length); i++) {
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
    out.definitionStart("program", "Program");
    out.incPrintln("PROG.Build_t");
    out.println("AllClasses");
    out.println("AllInterfaces");
    out.decPrintln(".\n");
    out.definitionStart("subclass");
    out.incPrintln();
    out.println("match P.subclass_test program with\n" + 
                "| Some f => f\n" + 
                "| None => fun x y => true\n" +
                "end");
    out.decPrintln(".\n");
    out.endModule(fNamingData.getModuleName() + "Program");
  }


  /**
   * Prints the prelude for the main file generation.
   * @param out the output stream
   */
  private void printMainPrelude(final CoqStream out) {
    printLoadPath(out);
    out.println(getImplemSpecif().getBeginning());
    out.reqImport("ImplemSWp");
    out.imprt("P");
    out.imprt("MDom");
    out.println();
    out.reqExport(fNamingData.getTypeName());
    out.reqExport(fNamingData.getSignatureName());
    
    out.exprt(fNamingData.getTypeModule());
    out.exprt(fNamingData.getSignatureModule());
    out.println();
  }



  /**
   * This method is called to generate the main makefile.
   */
  public void generateMainMakefile() {
    
    final MakefileGen mg = new MakefileGen(getBaseDir());
    mg.generate();
  }
  
  /**
   * This method is called to generate all the class make files
   * (the makefiles of the subdirectories).
   */
  public void generateClassMakefiles() {
    final ClassesMakefileGen cmg = new ClassesMakefileGen(getBaseDir(), 
                                                          getTreatedClasses());
    cmg.generate();
  }


  /**
   * Write the signature file.
   * 
   * @throws FileNotFoundException
   *             in case the file cannot be written
   */
  private void doSignature() throws FileNotFoundException {
    final File typ = new File(getBaseDir(), fNamingData.getSignatureFileName());
    /* final File typ = new File( fCoqName + "_signature" + suffix); */
    final CoqStream out = new CoqStream(new FileOutputStream(typ));
    printLoadPath(out);
    out.println(getImplemSpecif().getBeginning());
    
    out.println();
    out.startModule(fNamingData.getSignatureModule());
    
    // the special library
    for (int i = 0; !fGenerateJavaLibs && i < fSpecialLibs.length; i++) {
      final String str = getImplemSpecif().requireLib(Util.coqify(fSpecialLibs[i]));
      out.load(str + ".v");
    }
    out.println();
    // the already treated classes + interfaces
    for (Entry<String, ClassExecutor> ce : 
           fTreatedClasses.entrySet()) {
      out.load(ce.getValue().getModuleName() + "_signature.v");
    }
    
    out.endModule(fNamingData.getSignatureModule());
    out.close();
  
  }
  
  /**
   * Write the type file.
   * 
   * @throws FileNotFoundException
   *             if the type file cannot be created
   */
  private void doType() throws FileNotFoundException {
    final File typ = new File(getBaseDir(), fNamingData.getTypeFileName());
    final CoqStream out = new CoqStream(new FileOutputStream(typ));

    printLoadPath(out);
    out.println(getImplemSpecif().getBeginning());
    
    out.println();
    out.startModule(fNamingData.getTypeModule());

    
    // the special library
    for (int i = 0; !fGenerateJavaLibs && i < fSpecialLibs.length; i++) {
      final String str = getImplemSpecif().requireLib(Util.coqify(fSpecialLibs[i]));
      out.load(str + ".v");
    }
    out.println();
    // the already treated classes + interfaces
    for (Entry<String, ClassExecutor> ce : fTreatedClasses.entrySet()) {
      out.load(ce.getValue().getModuleName() + "_type.v");
    }
    
    out.endModule(fNamingData.getTypeModule());
    out.close();
  }


  /**
   * Print all the necessary load path instructions, as
   * well as the load for the special libraries.
   * @param out the out put file where to write the instructions.
   */
  private void printLoadPath(final CoqStream out) {
    for (String path: libPaths) {
      out.addLoadPath(new LoadPath(path));
    }
    final Set<String> set = new HashSet<String>();
    for (Entry<String, ClassExecutor> ce : fTreatedClasses.entrySet()) {
      final String pkg = "classes/" + ce.getValue().getPackageDir().toString();
      set.add(pkg);
    }
    
    // the special library
    for (int i = 0; !fGenerateJavaLibs && i < fSpecialLibs.length; i++) {
      final String str = getImplemSpecif().requireLib(Util.coqify(fSpecialLibs[i]));
      out.load(str + ".v");
    }
    out.println();
    
    for (String s: set) {
      out.addLoadPath(new LoadPath(s));
    }
  }
  
  /**
   * Write the dictionnary to a file.
   * 
   * @throws FileNotFoundException
   *             If there is a problem in writing.
   * @deprecated not used
   */
  public void writeDictionnary() throws FileNotFoundException {
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
    boolean res = false;
    if (fGenerateJavaLibs) {
      res = false;
    }
    else if (clname.startsWith("java")) {
      res =  true;
    }
    for (String lib: fSpecialLibs) {
      if (lib.equals(clname)) {
        res = true;
      }
    }
    return res;
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
  public ClassExecutor handleClass(final String clname) 
    throws ClassNotFoundException, IOException {
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
    return new ClassExecutor(this, cg);
  }
  
    
  /**
   * Define all classes and interfaces.
   * 
   * @throws IOException
   */
  private void defineClassAndInterface() {
    final IImplemSpecifics implem = getImplemSpecif();
    final CoqStream out = getOut();
    final List<ClassExecutor> treatedInterfaces = new ArrayList<ClassExecutor>();
    final List<ClassExecutor> treatedClasses = new ArrayList<ClassExecutor>(); 
    for (ClassExecutor ce: fTreatedClasses.values()) {
      if (ce.getJavaClass().isInterface()) {
        treatedInterfaces.add(ce);
      } 
      else {
        treatedClasses.add(ce);
      }
    }
    
    // all classes
    String clzzBody = "";
    for (ClassExecutor clss : treatedClasses) {
      clzzBody += implem.classCons(clss.getModuleName() + ".class");
    }
    if (!fGenerateJavaLibs) {
      for (String lib: fSpecialLibs) {
        clzzBody += implem.classCons(Util.coqify(lib) + ".class");
      }
    }
    clzzBody += " " + implem.classEnd();
    out.definition("AllClasses", implem.classType(), clzzBody);
    out.println();
    
    // all interfaces
    String interfBody = "";
    for (ClassExecutor interf : treatedInterfaces) {
      interfBody += implem.interfaceCons(interf.getModuleName() + ".interface");
    }
    interfBody += " " + implem.interfaceEnd();
    out.definition("AllInterfaces", implem.interfaceType(), interfBody);
  }
  
  /**
   * Returns the collection of all the classes that were 
   * translated.
   * @return a list of the classes
   */
  public Collection<ClassExecutor> getTreatedClasses() { 
    return fTreatedClasses.values();
  }

  /**
   * The different names of the modules, files for this
   * executor.
   * @return an instance of naming data.
   */
  public NamingData getNamingData() {
    return fNamingData;
  }
  
}
