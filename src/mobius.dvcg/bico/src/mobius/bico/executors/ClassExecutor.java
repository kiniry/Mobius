package mobius.bico.executors;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import mobius.bico.Util;
import mobius.bico.bicolano.coq.CoqStream;
import mobius.bico.bicolano.coq.LoadPath;
import mobius.bico.bicolano.coq.Translator;
import mobius.bico.implem.IImplemSpecifics;
import mobius.bico.visitors.DependenciesVisitor;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ClassGen;

/**
 * This class is used in the treatment of a single class by bico.
 * 
 * @author J. Charles (julien.charles@inria.fr), P. Czarnik
 *         (czarnik@mimuw.edu.pl), L. Hubert (laurent.hubert@irisa.fr)
 */
public class ClassExecutor extends ASignatureExecutor {

  /** the path to the libraries, relative to the package dir. */
  private final String fLibPath;
  
  /** the current class which is inspected. */
  private final ClassGen fClass;
  
  /** an executor to generate things concerning methods. */
  private final MethodExecutor fMethExecutor;
  
  /** an executor to generate things concerning fields. */
  private final FieldExecutor fFieldExecutor;
  
  /** the coqified naming informations for the class. */
  private final NamingData fNamingData;
    
  /** the real directory which corresponds to the current package. */
  private final File fWorkingDir;
  
  /** the set of the load path necessary for this class. */
  private final Set<LoadPath> fLoadPaths = new HashSet<LoadPath>();
  
  /** dependencies of the current class.   */
  private  final Set<NamingData> fExtLibsLocal = new HashSet<NamingData>();
  
  /** the executor which spawned this class executor. */
  private Executor fExecutor;

  /**
   * Create a class executor in the context of another executor.
   * 
   * @param exec the Executor to get the initialization from
   * @param cg the class object to manipulate
   * @throws FileNotFoundException
   *             if the file cannot be opened
   */
  public ClassExecutor(final Executor exec, 
                       final ClassGen cg) throws FileNotFoundException {
    super(exec, cg);
    fClass = cg;
    fExecutor = exec;
    fNamingData = new NamingData(fClass);
    fWorkingDir = new File(getBaseDir(), 
                           fNamingData.getPkgDir().getPath());
    setOut(new CoqStream(new FileOutputStream(
             new File(fWorkingDir, fNamingData.getBicoClassFileName()))));
    fFieldExecutor = new FieldExecutor(this, fClass.getJavaClass());
    fMethExecutor = new MethodExecutor(this, fClass);
    fLibPath = computePathToLibraries(); 
  }
  
  /**
   * Computes the add to load path instructions for Coq.
   * @return a String containing a serie of Add LoadPath
   */
  private String computePathToLibraries () {
    String pathToLib = ".." + File.separator;
    for (String s: fClass.getJavaClass().getPackageName().split("\\.")) {
      if (!s.equals("")) {
        pathToLib += ".." + File.separator;
      }
    }
    
    String res = "";
    for (String path: Executor.libPaths) {
      res += Translator.addLoadPath(new LoadPath(pathToLib + path)) + "\n";
    }
    res += Translator.addLoadPath(new LoadPath(pathToLib)) + "\n";
    return res;
  }
  
  
  /**
   * Real handling of one class in jc.
   * 
   * @throws ClassNotFoundException if a class cannot be resolved
   * @throws IOException if something cannot be written
   */
  @Override
  public void start() throws ClassNotFoundException, IOException {
  
    final JavaClass jc = fClass.getJavaClass();
    if (jc == null) {
      throw new NullPointerException();
    }
    getDico().addClass(jc);
    findDependencies();
    // first, handle the classes on which the current class depends
    /* initFOtherLibs(); */
    System.out.print("  --> Generating " + fNamingData.getTypeModule() + ": ");
    doType();
    System.out.println("done.");
    
    System.out.print("  --> Generating " + fNamingData.getSignatureModule() + ": ");
    doSignature();
    System.out.println("done.");
    
    System.out.print("  --> Generating " + fNamingData.getModuleName() + ": ");
    doMain();
    System.out.println("done.");
  

  
  }
  
  /**
   * 
   * Does the main file generation. This generates for instance the file
   * "test2_B.v", i.e. packageName_className.v
   * 
   * @throws ClassNotFoundException
   *             if there was a problem retrieving a field or a method
   */
  private void doMain() throws ClassNotFoundException {
    final CoqStream out = getOut();
    
    printMainPrelude(out);
    
    out.startModule(fNamingData.getModuleName());
    out.imprt(fNamingData.getTypeModule());
    out.imprt(fNamingData.getSignatureModule());
    
    fFieldExecutor.start();
    
    fMethExecutor.start();
    
    doClassDefinition();
    
    out.endModule(fNamingData.getModuleName());
    out.flush();
    out.close();
  }

  /**
   * Prints the prelude for the main file generation.
   * @param out the output stream
   */
  private void printMainPrelude(final CoqStream out) {
    final IImplemSpecifics implem = getImplemSpecif();
    out.println(fLibPath);
    printLoadPaths(out);
    
    out.println(implem.getBeginning());
    out.imprt("P");

    for (NamingData ex: fExtLibsLocal) {
      if (fExecutor.isSpecialLib(ex.getClassName())) {
        out.reqExport(implem.requireLib(ex.getModuleName()));
        out.exprt(ex.getSignatureModule());
      }
      else {
        out.reqExport(ex.getSignatureName());
        out.exprt(ex.getSignatureModule());
      }
    }

    out.reqImport(fExecutor.getNamingData().getTypeName());
    out.imprt(fExecutor.getNamingData().getTypeModule());

    out.reqImport(fExecutor.getNamingData().getSignatureName());
    out.imprt(fExecutor.getNamingData().getSignatureModule());

    out.println();
  }
  
  /**
   * Prints the signatures of the methods and fields.
   * 
   * @throws ClassNotFoundException
   *             in case of a field or a methods which corresponds to no
   *             class.
   */
  public void doSignature() throws ClassNotFoundException {
    
    printSignaturePrelude();
    
    
    fOutSig.startModule(fNamingData.getSignatureModule());
    fOutSig.imprt(fNamingData.getTypeModule());
    fFieldExecutor.doSignature();
    
    fMethExecutor.doSignature();
    
    fOutSig.endModule(fNamingData.getSignatureModule());
    fOutSig.flush();
    fOutSig.close();
  }
  /**
   * Prints the prelude for the Signature file generation.
   */
  private void printSignaturePrelude() {
    fOutSig.println(fLibPath);
    printLoadPaths(fOutSig);
    final IImplemSpecifics implem = getImplemSpecif();
    fOutSig.println(implem.getBeginning());
    fOutSig.imprt("P");
    fOutSig.println();
    
    for (NamingData ex: fExtLibsLocal) {
      if (fExecutor.isSpecialLib(ex.getClassName())) {
        fOutSig.reqExport(implem.requireLib(ex.getModuleName()));
        fOutSig.exprt(ex.getTypeModule());
      }
      else {
        fOutSig.reqExport(ex.getTypeName());
        fOutSig.exprt(ex.getTypeModule());
      }
    }
    fOutSig.reqImport(fExecutor.getNamingData().getTypeName());
    fOutSig.imprt(fExecutor.getNamingData().getTypeModule());
    fOutSig.println();
  }
  

  /**
   * Prints the load path necessary for a class, which involves dependencies.
   * @param out the output stream where to print the load path
   */
  private void printLoadPaths(final CoqStream out) {
    // store here the add load path statements
    for (LoadPath lp: fLoadPaths) {
      out.addLoadPath(lp, fWorkingDir);
    }
  }
  
  /**
   * Prints the class name definition of the current class.
   * 
   * @throws FileNotFoundException
   *             if the output file cannot be created
   */
  public void doType() throws FileNotFoundException {
    final JavaClass jc = fClass.getJavaClass();
    final int className = getDico().getCoqClassName(jc);
    final int packageName = getDico().getCoqPackageName(jc);
    /*
     * final File typeFile = new File(getBaseDir(), fModuleName +
     * "_type.v");
     */
    final File typeFile = new File(fWorkingDir, fNamingData.getTypeFileName());
    final CoqStream fOutTyp = new CoqStream(new FileOutputStream(typeFile));
    
    fOutTyp.println(fLibPath);
    
    fOutTyp.println(getImplemSpecif().getBeginning());
    fOutTyp.imprt("P");
    fOutTyp.startModule(fNamingData.getTypeModule());
    
    // classname
    if (jc.isInterface()) {
      fOutTyp.definition("name", "InterfaceName",
                         Translator.couple(packageName + "%positive", 
                                           className + "%positive"));
    } 
    else {
      fOutTyp.definition("name", "ClassName",
                         Translator.couple(packageName + "%positive",
                                           className + "%positive"));

    }
    
    fOutTyp.endModule(fNamingData.getTypeModule());
    fOutTyp.flush();
    fOutTyp.close();
  }
  
  /**
   * Do the proper class definition.
   */
  protected void doClassDefinition() {
    final CoqStream fOut = getOut();
    final JavaClass jc = fClass.getJavaClass();
    if (jc.isInterface()) {
      fOut.definitionStart("interface", "Interface");
      fOut.incPrintln("INTERFACE.Build_t");
      fOut.println("name");
    } 
    else {
      fOut.definitionStart("class", "Class");
      fOut.incPrintln("CLASS.Build_t");
      fOut.println("name");
      final String superClassName = Util.coqify(jc.getSuperclassName());
      if (superClassName == null) {
        fOut.println("None");
      } 
      else {
        fOut.println("(Some " + superClassName + "Type.name)");
      }
    }
    enumerateInterfaces();
    
    fFieldExecutor.doEnumeration();
    
    fMethExecutor.doEnumeration();
    
    fOut.println(jc.isFinal());
    fOut.println(jc.isPublic());
    fOut.println(jc.isAbstract());
    
    fOut.decPrintln(".\n");
  
  }
  
  /**
   * Enumerates the interfaces of the class.
   */
  private void enumerateInterfaces() {
    final CoqStream fOut = getOut();
    final String[] inames = fClass.getInterfaceNames();
    if (inames.length == 0) {
      fOut.println("nil");
    } 
    else {
      String str = "(";
      for (int i = 0; i < inames.length; i++) {
        str = str + Util.coqify(inames[i]) + ".name ::";
      }
      str = str.concat("nil)");
      fOut.println(str);
    }
  }
  
  /**
   * Returns the module name; a coqified name of the the full class name.
   * 
   * @return a string representing the module name
   */
  public String getModuleName() {
    return fNamingData.getModuleName();
  }
  
  /**
   * THIS IS THE METHOD WHICH RETURNS THE PATH + FILE WHICH WILL BE LOADED IN
   * X_MAP.v : "LOAD PATH + FILE" Returns the module name with the right
   * relative path.
   * 
   * @return a string representing the module name + the package dir
   */
  public String getModuleFileName() {
    final String pack = getPackageDir().getPath();
    final String mod = getModuleName();
    if (pack.equals("")) {
      return mod;
    } 
    else {
      return pack + File.separator + mod;
    }
  }
  
  /**
   * Returns the relative path to the file. It is a path relative to the base
   * directory, and it does not represents an existing physical one.
   * 
   * @return the path corresponding to the package
   */
  public File getPackageDir() {
    return fNamingData.getPkgDir();
  }
  
  /**
   * Returns the current working directory.
   * <code>baseDirectory + packageDirectory</code>
   * @return the content of the field {@link #fWorkingDir}
   */
  public File getWorkingDir() {
    return fWorkingDir;
  }
  
  /**
   * Return the bcel version of the class.
   * 
   * @return the class taken from the field {@link #fClass}
   */
  public JavaClass getJavaClass() {
    return fClass.getJavaClass();
  }
  
  /**
   * manages imported classes in the current class. If the imported class is
   * not already stored in the hash map then put it in the hash map of
   * external libraries and also add a load path to the class if such does not
   * exist already
   * 
   * @param clzz the class to load
   * @throws ClassNotFoundException if the specified class
   * does not exists
   */
  private void handleImportedLib(final String clzz)
    throws ClassNotFoundException {
    final String clname = clzz;
    NamingData cl = null;
    if (clname.equals("")) {
      return;
    }
    
    final JavaClass jc = getRepository().loadClass(clname);
    cl = new NamingData(jc);
    fExtLibsLocal.add(cl);
    extractLoadPath(cl);    
  }
  
  /**
   * the method searches for all references to other classes in the current
   * class and adds them in the list of class types
   * {@link #fExtLibs fOtherLibs} to be processed. This means that for their
   * corresponding class files their respective bicolano version will be
   * generated. The identification of such files is done by
   * <ul>
   * <li> identifying the types of the instance fields.
   * <li> identifying constant field reference elements in the constant pool
   * <li> identifying the type of the arguments and the result of the invoked
   * methods in the class
   * </ul>
   * 
   * @throws ClassNotFoundException if one of the class dependencies cannot be resolved
   */
  private void findDependencies() throws ClassNotFoundException {
    final JavaClass jc = fClass.getJavaClass();
    final Collection<String> deps = DependenciesVisitor.getDependencies(jc);
    for (String str: deps) {
      handleImportedLib(str);
    }
  }
  
  
 
  
  /**
   * Adds a load path to this class if such a path does not already exists.
   * 
   * @param cl the external class to which a load path is added
   */
  private void extractLoadPath(final NamingData cl) {
    final File f = new File(getBaseDir(), cl.getClassFile().getPath());
    // if the file exists in the base directory of the current application
    // and the path is not already such path then add it
    if (f.exists()) {
      fLoadPaths.add(new LoadPath(f.getParent()));
    }
  }
  
  /**
   * Returns the list of all the classes that are used by this class.
   * @return a valid list of the dependencies
   */
  public List<String> getClassDependencies() {
    final List<String> al = new ArrayList<String>();
    for (NamingData ec : fExtLibsLocal) {
      al.add(ec.getClassName());
    }
    return al;
  }
  
  /**
   * @return "Class Executor: module_name.
   */
  @Override
  public String toString () {
    return "Class Executor: " + getModuleName();
  }
  
  /**
   * Returns the path to the library, relative to the package
   * dir.
   * @return a non null string
   */
  public String getLibPath() {
    return fLibPath;
  }

}
