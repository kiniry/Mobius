package mobius.bico;

import mobius.bico.MethodHandler.MethodNotFoundException;

import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;

public class ClassExecutor extends ABasicExecutor {
  private ClassGen cg;


  /**
   * @param jc the current class
   * @param packageName the index representing the package
   * @param className the number representing the class
   */
  public ClassExecutor(ABasicExecutor be, ClassGen cg, int pkgName) {
    super(be);
    this.cg = cg;
  }
  
  /**
   * Real handling of one class in jc.
   * 
   * @throws ClassNotFoundException if a class cannot be resolved
   */
  public void start() throws ClassNotFoundException {

    int tab = 1;
    final JavaClass jc = cg.getJavaClass();
    final String moduleName = Util.coqify(jc.getClassName());
    System.out.println("  --> Module " + moduleName + ".");
    Util.writeln(fOut, tab, "Module " + moduleName + ".");
    fOut.println();

    

    final int className = fDico.getCurrentClass() + 1;
    fDico.addClass(jc, className);
    
    tab++;
    int packageName = fDico.getCoqPackageName(jc);
    // classname
    if (jc.isInterface()) {
      final String str = "Definition interfaceName : InterfaceName := " + "(" + 
                          packageName + ", " + className + "%positive).";
      Util.writeln(fOut, tab, str);
    } 
    else {
      final String str = "Definition className : ClassName := " + "(" + 
                         packageName + 
                         ", " + className + "%positive).";
      Util.writeln(fOut, tab, str);
    }

    fOut.println();
    final FieldExecutor fieldExecutor = new FieldExecutor(this, jc);
    fieldExecutor.start();
    final MethodExecutor methExecutor = new MethodExecutor(this, cg);
    methExecutor.start();

    doClassDefinition(jc);
    fOut.println();
    tab--;
    Util.writeln(fOut, tab, "End " + Util.coqify(jc.getClassName()) + ".");
    fOut.println();
  }




 

  private void doClassDefinition(final JavaClass jc) {
    final int tab = 2;
    
    if (jc.isInterface()) {
      Util.writeln(fOut, tab, "Definition interface : Interface := INTERFACE.Build_t");
      Util.writeln(fOut, tab + 1, "interfaceName");
    } 
    else {
      Util.writeln(fOut, tab, "Definition class : Class := CLASS.Build_t");
      Util.writeln(fOut, tab + 1, "className");
    }
    if (!jc.isInterface()) {
      final String superClassName = Util.coqify(jc.getSuperclassName());
      if (superClassName == null) {
        Util.writeln(fOut, tab + 1, "None");
      } 
      else {
        Util.writeln(fOut, tab + 1, "(Some " + superClassName + ".className)");
      }
    }
    final String[] inames = jc.getInterfaceNames();
    if (inames.length == 0) {
      Util.writeln(fOut, tab + 1, "nil");
    } 
    else {
      String str = "(";
      for (int i = 0; i < inames.length; i++) {
        str = str.concat(Util.coqify(inames[i]) + ".interfaceName ::");
      }
      str = str.concat("nil)");
      Util.writeln(fOut, tab + 1, str);
    }

    // fields
    final Field[] ifield = jc.getFields();
    if (ifield.length == 0) {
      Util.writeln(fOut, tab + 1, fImplemSpecif.getNoFields());
    } 
    else {
      String str2 = "(";
      for (int i = 0; i < ifield.length - 1; i++) {
        str2 += fImplemSpecif.fieldsCons(Util.coqify(ifield[i].getName()) + "Field");
      }
      str2 += fImplemSpecif.fieldsEnd(Util.coqify(ifield[ifield.length - 1].getName()) + 
                                      "Field");
      str2 += ")";
      Util.writeln(fOut, tab + 1, str2);
    }

    // methods
    final Method[] imeth = jc.getMethods();
    if (imeth.length == 0) {
      // System.out.println(" nil");
      Util.writeln(fOut, tab + 1, fImplemSpecif.getNoMethods());
    } 
    else {
      String str2 = "(";
      for (int i = 0; i < imeth.length - 1; i++) {

        try {
          str2 += fImplemSpecif.methodsCons(fMethodHandler.getName(imeth[i]) + "Method");
        } 
        catch (MethodNotFoundException e) {
          e.printStackTrace(); // cannot happen
          System.exit(1);
        }
      }
      str2 += fImplemSpecif.methodsEnd(Util.coqify(imeth[imeth.length - 1].getName()) +
                                       "Method");
      str2 += ")";
      Util.writeln(fOut, tab + 1, str2);
    }

    Util.writeln(fOut, tab + 1, "" + jc.isFinal());
    Util.writeln(fOut, tab + 1, "" + jc.isPublic());
    Util.writeln(fOut, tab + 1, "" + jc.isAbstract());
    Util.writeln(fOut, tab, ".");
  }

}
