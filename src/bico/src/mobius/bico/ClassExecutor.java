package mobius.bico;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;

import mobius.bico.Util.Stream;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ClassGen;

/**
 * This class is used in the treatment of a single class
 * by bico.
 * 
 * @author J. Charles (julien.charles@inria.fr), 
 * P. Czarnik (czarnik@mimuw.edu.pl), 
 * L. Hubert (laurent.hubert@irisa.fr)
 */
public class ClassExecutor extends ASignatureExecutor {
  /** the standard lib paths. */
  //FIXME: should be relative to the package dir
  private static final String libPath = 
                      "Add LoadPath \"Formalisation/Library\".\n" + 
                      "Add LoadPath \"Formalisation/Library/Map\".\n" +
                      "Add LoadPath \"Formalisation/Bicolano\".\n";


  /** the current class which is inspected. */
  private ClassGen fClass;
  

  /** an executor to generate things concerning methods. */
  private MethodExecutor fMethExecutor;
  
  /** an executor to generate things concerning fields. */
  private FieldExecutor fFieldExecutor;

  /** the file that will be the output of the executor. */
  private File fOutputFile;

  /** the coqified name of the class (package + classname). */
  private String fModuleName;

  /** the directory which corresponds to the current package. */
  private File fPackageDir;
  
  /** the real directory which corresponds to the current package. */
  private File fWorkingDir;


  protected String fName;
  
  
  /**
   * Create a class executor in the context of another
   * executor.
   * @param be the BasicExecutor to get the initialization from
   * @param cg the class object to manipulate
   * @param baseDir the current working directory
   * @param name the name of the main file
   * @throws FileNotFoundException if the file cannot be opened
   */
  public ClassExecutor(final ABasicExecutor be, final ClassGen cg,
                       final File baseDir, final String name) throws FileNotFoundException {
    super(be, baseDir, cg);
    fClass = cg;
    fName = name;
    final JavaClass jc = fClass.getJavaClass();
    
    
    fModuleName = Util.coqify(jc.getClassName());

    fPackageDir = new File(jc.getPackageName().replace('.', File.separatorChar));
    fWorkingDir = new File(baseDir, fPackageDir.getPath());
    
    fOutputFile = new File(fWorkingDir, fModuleName + ".v");    
    fOut = new Util.Stream(new FileOutputStream(fOutputFile));

    fFieldExecutor = new FieldExecutor(this, fClass.getJavaClass());
    fMethExecutor = new MethodExecutor(this, fClass);
  }

  /**
   * Real handling of one class in jc.
   * 
   * @throws ClassNotFoundException if a class cannot be resolved
   * @throws FileNotFoundException if the type stream cannot be created
   */
  @Override
  public void start() throws ClassNotFoundException, FileNotFoundException {

    final JavaClass jc = fClass.getJavaClass(); 
    final int className = fDico.getCurrentClass() + 1;
    fDico.addClass(jc, className); 
    System.out.print("  --> Generating " + fModuleName + "Type: ");    
    doType();
    System.out.println("done.");
    
    System.out.print("  --> Generating " + fModuleName + "Signature: ");
    doSignature();
    System.out.println("done.");
    
    System.out.print("  --> Generating " + fModuleName + ":");
    
    fOut.println(libPath);
    fOut.println("Require Import ImplemProgramWithMap.\n" +
                    "Import P.\n");
    fOut.println("Require Import " + fName + "_signature.");
    fOut.println("Require Import " + fName + "_type.");
    fOut.println("Import " + fName + "Signature.");
    fOut.println("Import " + fName + "Type.");
    fOut.println();
    
    fOut.incPrintln("Module " + fModuleName + ".\n");
    fOut.println("Import "  + fModuleName + "Type.");
    fOut.println("Import "  + fModuleName + "Signature.");
    
    
    fFieldExecutor.start();
    
    
    fMethExecutor.start();

    doClassDefinition();
   
    fOut.decPrintln("End " + fModuleName + ".\n");
    System.out.println("done.");

  }
  
  /**
   * Prints the signatures of the methods and fields.
   * @throws ClassNotFoundException in case of a field or a 
   * methods which corresponds to no class.
   */
  public void doSignature() throws ClassNotFoundException {
    fOutSig.println(libPath);
    fOutSig.println("Require Import ImplemProgramWithMap.\n" +
                    "Import P.\n");
    fOutSig.println("Require Import " + fModuleName + "_type.");
    fOutSig.println("Import "  + fModuleName + "Type.\n");
    
    fOutSig.incPrintln("Module " + fModuleName + "Signature.\n");
  
    fFieldExecutor.doSignature();

    fMethExecutor.doSignature();
  
    fOutSig.decPrintln("End " + fModuleName + "Signature.\n");
    
  }

  /**
   * Prints the class name definition of the current class.
   * @throws FileNotFoundException if the output file cannot be created
   */
  public void doType() throws FileNotFoundException {
    final JavaClass jc = fClass.getJavaClass();
    final int className =  fDico.getCoqClassName(jc);
    final int packageName = fDico.getCoqPackageName(jc);
    final File typeFile = new File(fWorkingDir, fModuleName + "_type.v");
    final Stream  fOutTyp = new Util.Stream(new FileOutputStream(typeFile));
    
    
    fOutTyp.println(libPath);
    
    fOutTyp.println("Require Import ImplemProgramWithMap.\n" +
                    "Import P.\n");
    fOutTyp.incPrintln("Module " + fModuleName + "Type.\n");
    
    // classname
    String def;
    if (jc.isInterface()) {
      def = "Definition interfaceName : InterfaceName := " + "(" + 
                          packageName + "%positive, " + className + "%positive).\n";
    } 
    else {
      def = "Definition className : ClassName := " + "(" + 
                         packageName + 
                         "%positive, " + className + "%positive).\n";
      
    }
    fOutTyp.println(def);

    fOutTyp.decPrintln("End " + fModuleName + "Type.\n");
    
  }


  /**
   * Do the proper class definition.
   */
  protected void doClassDefinition() {
    final JavaClass jc = fClass.getJavaClass(); 
    if (jc.isInterface()) {
      fOut.incPrintln("Definition interface : Interface := INTERFACE.Build_t");
      fOut.println("interfaceName");
    } 
    else {
      fOut.incPrintln("Definition class : Class := CLASS.Build_t");
      fOut.println("className");
      final String superClassName = Util.coqify(jc.getSuperclassName());
      if (superClassName == null) {
        fOut.println("None");
      } 
      else {
        fOut.println("(Some " + superClassName + ".className)");
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
    final String[] inames = fClass.getInterfaceNames();
    if (inames.length == 0) {
      fOut.println("nil");
    } 
    else {
      String str = "(";
      for (int i = 0; i < inames.length; i++) {
        str = str.concat(Util.coqify(inames[i]) + ".interfaceName ::");
      }
      str = str.concat("nil)");
      fOut.println(str);
    }
  }

  /**
   * Return the relative path to the output file.
   * @return a file which has its relative path valid
   */
  public File getOuputFile() {
    return fOutputFile;
  }

  public String getModuleName() {
    return fModuleName;
  }
  
  public File getPackageDir() {
    return fPackageDir;
  }

}
