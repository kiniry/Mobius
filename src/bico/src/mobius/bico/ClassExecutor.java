package mobius.bico;

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
class ClassExecutor extends ABasicExecutor {
  
  /** the current class which is inspected. */
  private ClassGen fClass;
  
  /** the current tabulation level. */
  private int fTab = 1;

  /** an executor to generate things concerning methods. */
  private MethodExecutor fMethExecutor;
  
  /** an executor to generate things concerning fields. */
  private FieldExecutor fFieldExecutor;

  /**
   * Create a class executor in the context of another
   * executor.
   * @param be the BasicExecutor to get the initialization from
   * @param cg the class object to manipulate
   */
  public ClassExecutor(final ABasicExecutor be, final ClassGen cg) {
    super(be);
    fClass = cg;
    fFieldExecutor = new FieldExecutor(this, fClass.getJavaClass());
    fMethExecutor = new MethodExecutor(this, fClass);
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
    Util.writeln(fOut, fTab, "Module " + moduleName + ".\n");

    final int className = fDico.getCurrentClass() + 1;
    fDico.addClass(jc, className);
    
    fTab++;
    
    doClassNameDefinition();
 
    
    fFieldExecutor.start();
    
    
    fMethExecutor.start();

    doClassDefinition();
   
    fTab--;
    Util.writeln(fOut, fTab, "End " + moduleName + ".\n");

  }

  /**
   * Prints the class name definition of the current class.
   */
  private void doClassNameDefinition() {
    final JavaClass jc = fClass.getJavaClass();
    final int className =  fDico.getCoqClassName(jc);
    final int packageName = fDico.getCoqPackageName(jc);
    // classname
    String def;
    if (jc.isInterface()) {
      def = "Definition interfaceName : InterfaceName := " + "(" + 
                          packageName + ", " + className + "%positive).\n";
    } 
    else {
      def = "Definition className : ClassName := " + "(" + 
                         packageName + 
                         ", " + className + "%positive).\n";
      
    }
    Util.writeln(fOut, fTab, def);
  }


  /**
   * Do the proper class definition.
   */
  private void doClassDefinition() {
    final JavaClass jc = fClass.getJavaClass(); 
    if (jc.isInterface()) {
      Util.writeln(fOut, fTab, "Definition interface : Interface := INTERFACE.Build_t");
      Util.writeln(fOut, fTab + 1, "interfaceName");
    } 
    else {
      Util.writeln(fOut, fTab, "Definition class : Class := CLASS.Build_t");
      Util.writeln(fOut, fTab + 1, "className");
      final String superClassName = Util.coqify(jc.getSuperclassName());
      if (superClassName == null) {
        Util.writeln(fOut, fTab + 1, "None");
      } 
      else {
        Util.writeln(fOut, fTab + 1, "(Some " + superClassName + ".className)");
      }
    }
    enumerateInterfaces();

    fFieldExecutor.doEnumeration(fTab);

    fMethExecutor.doEnumeration(fTab);

    Util.writeln(fOut, fTab + 1, "" + jc.isFinal());
    Util.writeln(fOut, fTab + 1, "" + jc.isPublic());
    Util.writeln(fOut, fTab + 1, "" + jc.isAbstract());
    Util.writeln(fOut, fTab, ".\n");
  }

  /**
   * Enumerates the interfaces of the class.
   */
  private void enumerateInterfaces() {
    
    final String[] inames = fClass.getInterfaceNames();
    if (inames.length == 0) {
      Util.writeln(fOut, fTab + 1, "nil");
    } 
    else {
      String str = "(";
      for (int i = 0; i < inames.length; i++) {
        str = str.concat(Util.coqify(inames[i]) + ".interfaceName ::");
      }
      str = str.concat("nil)");
      Util.writeln(fOut, fTab + 1, str);
    }
  }

  


}
