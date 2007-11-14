package mobius.bico.executors;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import mobius.bico.Util;
import mobius.bico.coq.CoqStream;
import mobius.bico.coq.LoadPath;
import mobius.bico.implem.IImplemSpecifics;

import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantCP;
import org.apache.bcel.classfile.ConstantFieldref;
import org.apache.bcel.classfile.ConstantMethodref;
import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ReferenceType;
import org.apache.bcel.generic.Type;

/**
 * This class is used in the treatment of a single class by bico.
 * 
 * @author J. Charles (julien.charles@inria.fr), P. Czarnik
 *         (czarnik@mimuw.edu.pl), L. Hubert (laurent.hubert@irisa.fr)
 */
public class ClassExecutor extends ASignatureExecutor {

  // FIXME: should be relative to the package dir
  private final String fLibPath;
  
  /** the coq version*/
  private final String fFileName;
  
  /** the current class which is inspected. */
  private ClassGen fClass;
  
  /** an executor to generate things concerning methods. */
  private final MethodExecutor fMethExecutor;
  
  /** an executor to generate things concerning fields. */
  private final FieldExecutor fFieldExecutor;
  
  /** the coqified name of the class (package + classname). */
  private String fModuleName;
  
  /** the directory which corresponds to the current package. */
  private File fPackageDir;
  
  /** the real directory which corresponds to the current package. */
  private File fWorkingDir;
  
  private final Map<String, LoadPath> loadPaths = new HashMap<String, LoadPath>();
  /*
   * private final HashMap<String, Import> imports = new HashMap<String,
   * Import>(); private final HashMap<String, Export> exports = new HashMap<String,
   * Export>();
   */
  /** the name of the library file where the whole program should be written. */
  /*
   * private String fName;
   */
  
  // /** the executor which spawned this class executor. */
  // private final Executor fExecutor;
  
  /** dependencies of the current class.   */
  private  final Map<String, ExternalClass> fExtLibsLocal = 
    new HashMap<String, ExternalClass>();
  private Executor fExec;

  /**
   * Create a class executor in the context of another executor.
   * 
   * @param exec the Executor to get the initialization from
   * @param cg the class object to manipulate
   * @param name the name of the main file
   * @throws FileNotFoundException
   *             if the file cannot be opened
   */
  public ClassExecutor(final Executor exec, 
                       final ClassGen cg,
                       final String name) throws FileNotFoundException {
    super(exec, cg);
    fClass = cg;
    fFileName = Util.coqify(cg.getClassName());

    final JavaClass javaClass = fClass.getJavaClass();
    fExec = exec;
    fModuleName = Util.coqify(javaClass.getClassName());
    
    fPackageDir = new File(javaClass.getPackageName().replace('.',
                                                              File.separatorChar));
    /* fWorkingDir = new File(exec.getBaseDir(), fPackageDir.getPath()); */
    fWorkingDir = new File(getBaseDir(), fPackageDir.getPath());
    
    // WRITE THE FILE in directory fWorkingDir
    setOut(new CoqStream(new FileOutputStream(new File(fWorkingDir,
                                                         fModuleName + ".v"))));
    
    fFieldExecutor = new FieldExecutor(this, fClass.getJavaClass());
    fMethExecutor = new MethodExecutor(this, fClass);
    String pathToLib = ".." + File.separator;
    for (String s: javaClass.getPackageName().split("\\.")) {
      if (!s.equals("")) {
        pathToLib += ".." + File.separator;
      }
    }
    fLibPath = 
      "Add LoadPath \"" + pathToLib + "Formalisation/Library\".\n" + 
      "Add LoadPath \"" + pathToLib + "Formalisation/Library/Map\".\n" + 
      "Add LoadPath \"" + pathToLib + "Formalisation/Bicolano\".\n";
  }
  
  /**
   * Real handling of one class in jc.
   * 
   * @throws ClassNotFoundException
   *             if a class cannot be resolved
   * @throws IOException
   */
  @Override
  public void start() throws ClassNotFoundException, IOException {
  
    final JavaClass jc = fClass.getJavaClass();
    if (jc == null) {
      throw new NullPointerException();
    }
    getDico().addClass(jc);
    initFOtherLibs();
    // first, handle the classes on which the current class depends
    /* initFOtherLibs(); */
    System.out.print("  --> Generating " + fModuleName + "Type: ");
    doType();
    System.out.println("done.");
    
    System.out.print("  --> Generating " + fModuleName + "Signature: ");
    doSignature();
    System.out.println("done.");
    
    System.out.print("  --> Generating " + fModuleName + ": ");
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
    final CoqStream fOut = getOut();
    fOut.println(fLibPath);
    fOut.println(Constants.REQ_IMPORT + 
                 "ImplemProgramWithMap.\n");
    fOut.println(Constants.IMPORT + "P.\n");
    fOut.println(Constants.REQ_IMPORT + fFileName + "_signature.");
    fOut.println(Constants.REQ_IMPORT + fFileName
    		+ "_type.");
    fOut.println(Constants.IMPORT + fFileName
    		+ "Signature.");
    fOut.println(Constants.IMPORT + fFileName + "Type.");
    fOut.println();
    
    fOut.incPrintln(Constants.MODULE + fModuleName
    		+ ".\n");
    fOut
    		.println(Constants.IMPORT + fModuleName + "Type.");
    fOut.println(Constants.IMPORT + fModuleName
    		+ "Signature.");
    
    fFieldExecutor.start();
    
    fMethExecutor.start();
    
    doClassDefinition();
    
    fOut.decPrintln(Constants.END_MODULE + fModuleName + ".\n");
    fOut.flush();
    fOut.close();
  }
  
  /**
   * Prints the signatures of the methods and fields.
   * 
   * @throws ClassNotFoundException
   *             in case of a field or a methods which corresponds to no
   *             class.
   */
  public void doSignature() throws ClassNotFoundException {
    
    fOutSig.println(fLibPath);
    String loadPathsForDep = printLoadPaths();
    fOutSig.println(loadPathsForDep);
    final IImplemSpecifics implem = getImplemSpecif();
    fOutSig.println(implem.getBeginning());
    fOutSig.imprt("P");
    fOutSig.reqImport(fFileName + "_type");
    fOutSig.imprt(fFileName + "Type");
    fOutSig.println();
    
    for (ExternalClass ex: fExtLibsLocal.values()) {
      if (fExec.isSpecialLib(ex.getClassName())) {
        fOutSig.reqExport(implem.requireLib(ex.getBicoClassName()));
        fOutSig.exprt(ex.getTypeModule());
      }
      else {
        fOutSig.reqExport(ex.getTypeName());
        fOutSig.exprt(ex.getTypeModule());
      }
    }
    fOutSig.println();
    fOutSig.startModule(fModuleName + "Signature");
    fOutSig.imprt(fModuleName + "Type");
    fFieldExecutor.doSignature();
    
    fMethExecutor.doSignature();
    
    fOutSig.endModule(fModuleName + "Signature");
    fOutSig.flush();
    fOutSig.close();
  }
  
  private void printImportedClasses(CoqStream out) {		
    out = getOut();
    for (ExternalClass ex: fExtLibsLocal.values()) {
      out.reqExport(ex.getTypeName());
      out.exprt(ex.getTypeModule());
    }
    
  }
  
  private String printLoadPaths() {
    // store here the add load path statements
    String s = "";
    for (LoadPath lp: loadPaths.values()) {
      s = s + lp.printRelative(fWorkingDir);
    }
    return s;
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
    final File typeFile = new File(fWorkingDir, fModuleName + "_type.v");
    final CoqStream fOutTyp = new CoqStream(new FileOutputStream(typeFile));
    
    fOutTyp.println(fLibPath);
    
    fOutTyp.println(getImplemSpecif().getBeginning());
    fOutTyp.imprt("P");
    fOutTyp.startModule(fModuleName + "Type");
    
    // classname
    String def;
    if (jc.isInterface()) {
      def = "Definition name : InterfaceName := " + 
            "(" + packageName + "%positive, " + className + "%positive).\n";
    } 
    else {
      def = "Definition name : ClassName := " + 
            "(" + packageName + "%positive, " + className + "%positive).\n";
    
    }
    fOutTyp.println(def);
    
    fOutTyp.endModule(fModuleName + "Type");
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
    	fOut.incPrintln("Definition interface : Interface := INTERFACE.Build_t");
    	fOut.println("name");
    } else {
    	fOut.incPrintln("Definition class : Class := CLASS.Build_t");
    	fOut.println("name");
    	final String superClassName = Util.coqify(jc.getSuperclassName());
    	if (superClassName == null) {
    		fOut.println("None");
    	} else {
    		fOut.println("(Some " + superClassName + "Type.name)");
    	}
    }
    enumerateInterfaces();
    
    fFieldExecutor.doEnumeration();
    
    fMethExecutor.doEnumeration();
    
    fOut.println("" + jc.isFinal());
    fOut.println("" + jc.isPublic());
    fOut.println("" + jc.isAbstract());
    
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
    return fModuleName;
  }
  
  /**
   * THIS IS THE METHOD WHICH RETURNS THE PATH + FILE WHICH WILL BE LOADED IN
   * X_MAP.v : "LOAD PATH + FILE.V" Returns the module name with the right
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
    return fPackageDir;
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
   * @param clzz
   * @throws ClassNotFoundException
   * @throws IOException
   */
  protected void handleImportedLib(final String clzz)
  		throws ClassNotFoundException, IOException {
    final String clname = clzz;
    if (clname == null) {
      return;
    }

  
    // if the class file is not already in the hash map of imported classes
    // then add it
    if ((fExtLibsLocal.get(clname) == null)) {
      final ExternalClass cl = new ExternalClass(clname);
      fExtLibsLocal.put(clname, cl);
      extractLoadPath(cl);
    }
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
   * @throws IOException
   * @throws ClassNotFoundException
   */
  protected void initFOtherLibs() throws ClassNotFoundException, IOException {
    final JavaClass jc = fClass.getJavaClass();
    final ConstantPool cp = jc.getConstantPool();
    final Constant[] co = cp.getConstantPool();
    for (int i = 0; i < co.length; i++) {
      ConstantCP c = null;
      if (cp.getConstant(i) instanceof ConstantFieldref) {
        c = (ConstantFieldref) co[i];
        final int k = c.getNameAndTypeIndex();
        final ConstantNameAndType nt = (ConstantNameAndType) cp.getConstant(k);
        String type = nt.getSignature(cp);
        
        type = Util.classFormatName2Standard(type);
        handleImportedLib(type);
        
        // addToOtherLibs(type);
      } 
      else if (cp.getConstant(i) instanceof ConstantMethodref) {
        c = (ConstantMethodref) co[i];
        String typeWhereDecl = c.getClass(cp);
        typeWhereDecl = Util.classFormatName2Standard(typeWhereDecl);
        handleImportedLib(typeWhereDecl);
      
      }
    }
    
    final Field[] fs = jc.getFields();
    for (int i = 0; i < fs.length; i++) {
      String type = fs[i].getSignature();
      type = Util.classFormatName2Standard(type);
      handleImportedLib(type);
    
    }
    
    final Method[] ms = jc.getMethods();
    for (Method met: ms) {
      final Type retT = met.getReturnType();
      if ((retT instanceof ArrayType) && 
          (((ArrayType) retT).getBasicType() instanceof ReferenceType)) {
        handleImportedLib(((ArrayType) retT).getBasicType().toString());
      } 
      else if ((!(retT instanceof ArrayType)) && 
               retT instanceof ReferenceType) {
        handleImportedLib(retT.toString());
      }
    
      final Type[] argT = met.getArgumentTypes();
      if (argT != null) {
        for (int k = 0; k < argT.length; k++) {
          if ((argT[k] instanceof ArrayType) && 
              (((ArrayType) argT[k]).getBasicType() instanceof ReferenceType)) {
            handleImportedLib(((ArrayType) argT[k]).getBasicType().toString());
          } 
          else if ((!(argT[k] instanceof ArrayType)) && 
                   argT[k] instanceof ReferenceType) {
            handleImportedLib(argT[k].toString());
          }
        }
      }
    
    }
  
  }
  
  /**
   * Adds a load path to this class if such a path does not already exists.
   * 
   * @param cl -
   *            the external class to which a load path is added
   */
  private void extractLoadPath(final ExternalClass cl) {
    File f = new File(getBaseDir(), cl.getClassName());
    // if the file exists in the base directory of the current application
    // and the path is not already such path then add it
    if (f.exists() && (loadPaths.get(f.getParent()) == null)) {
      loadPaths.put(f.getParent(), new LoadPath(f.getParent()));
      return;
    }
    f = new File(getPathToAPI(), cl.getClassName());
    // if the file exists in the API directory of the current application
// and the path is not already such path then add it
    if ((f.isFile()) && (loadPaths.get(f.getParent()) == null)) {
      loadPaths.put(f.getParent(), new LoadPath(f.getParent()));
      return;
    }
  }
  
  /**
   * Returns the list of all the classes that are used by this class.
   * @return a valid list of the dependencies
   */
  public List<String> getClassDependencies() {
    final List<String> al = new ArrayList<String>();
    al.addAll(fExtLibsLocal.keySet());
    return al;
  }
  
  public String toString () {
    return getModuleName();
  }

}
