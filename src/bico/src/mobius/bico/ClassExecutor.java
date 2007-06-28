package mobius.bico;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;

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
public class ClassExecutor extends ABasicExecutor {
  
  /** the current class which is inspected. */
  private ClassGen fClass;
  

  /** an executor to generate things concerning methods. */
  private MethodExecutor fMethExecutor;
  
  /** an executor to generate things concerning fields. */
  private FieldExecutor fFieldExecutor;

  /** the file that will be the output of the executor. */
  private File fOutputFile;

  /**
   * Create a class executor in the context of another
   * executor.
   * @param be the BasicExecutor to get the initialization from
   * @param cg the class object to manipulate
   * @param workingDir the current working directory
   * @throws FileNotFoundException if the file cannot be opened
   */
  public ClassExecutor(final ABasicExecutor be, final ClassGen cg,
                       final File workingDir) throws FileNotFoundException {
    super(be);
    fClass = cg;
    fOutputFile = determineFileName(workingDir);
    fOut = new Util.Stream(new FileOutputStream(new File(workingDir, fOutputFile.getPath())));
    fFieldExecutor = new FieldExecutor(this, fClass.getJavaClass());
    fMethExecutor = new MethodExecutor(this, fClass);
  }
 
  /**
   * Determine the file name of the output file.
   * @param workingDir the current working directory
   * @return a File which
   */
  private File determineFileName(final File workingDir) {
    final JavaClass jc = fClass.getJavaClass(); 
    final File dir = new File(jc.getPackageName().replace('.', File.separatorChar));
    new File(workingDir, dir.getPath()).mkdirs();
    return new File(dir, Util.coqify(jc.getClassName()) + ".v");
  }

  /**
   * Real handling of one class in jc.
   * 
   * @throws ClassNotFoundException if a class cannot be resolved
   */
  @Override
  public void start() throws ClassNotFoundException {

    final JavaClass jc = fClass.getJavaClass();
    final String moduleName = Util.coqify(jc.getClassName());
    System.out.println("  --> Module " + moduleName + ".");
    fOut.println("Module " + moduleName + ".\n");
    
    final int className = fDico.getCurrentClass() + 1;
    fDico.addClass(jc, className);
    
    fOut.incTab();
    
    doClassNameDefinition();
 
    
    fFieldExecutor.start();
    
    
    fMethExecutor.start();

    doClassDefinition();
   
    fOut.decTab();
    fOut.println("End " + moduleName + ".\n");

  }

  /**
   * Prints the class name definition of the current class.
   */
  public void doClassNameDefinition() {
    final JavaClass jc = fClass.getJavaClass();
    final int className =  fDico.getCoqClassName(jc);
    final int packageName = fDico.getCoqPackageName(jc);
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
    fOut.println(def);
  }


  /**
   * Do the proper class definition.
   */
  public void doClassDefinition() {
    final JavaClass jc = fClass.getJavaClass(); 
    if (jc.isInterface()) {
      fOut.println("Definition interface : Interface := INTERFACE.Build_t");
      fOut.incTab();
      fOut.println("interfaceName");
    } 
    else {
      fOut.println("Definition class : Class := CLASS.Build_t");
      fOut.incTab();
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
    fOut.decTab();
    fFieldExecutor.doEnumeration();

    fMethExecutor.doEnumeration();
    fOut.incTab();
    fOut.println("" + jc.isFinal());
    fOut.println("" + jc.isPublic());
    fOut.println("" + jc.isAbstract());
    fOut.decTab();
    fOut.println(".\n");

  }

  /**
   * Enumerates the interfaces of the class.
   */
  private void enumerateInterfaces() {
    fOut.incTab();
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
    fOut.decTab();
  }

  /**
   * Return the relative path to the output file.
   * @return a file which has its relative path valid
   */
  public File getOuputFile() {
    return fOutputFile;
  }


}
