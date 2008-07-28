package mobius.bico.dico;

import java.io.PrintStream;
import java.util.Collection;

import mobius.bico.dico.ClassConstants.Clss;
import mobius.bico.dico.ClassConstants.Meth;
import mobius.bico.dico.ClassConstants.Pkg;

import org.apache.bcel.classfile.JavaClass;


/**
 * The dictonary creates a dictonary that can then be used to translate the
 * generated name into human-readable names.
 * 
 * @author Laurent.Hubert@irisa.fr
 */
public abstract class ADictionary {

  /** determine the span of the 'reserved' class names number default is 20. */
  public static final int RESERVED_CLASSES = 20;
  
  /** determine the span of the 'reserved' packages names number default is 10. */
  //FIXME: should maybe be Pkg.values().length instead
  public static final int RESERVED_PACKAGES = 10; 

  /**
   * Associate package implementation name coqPackageName to the corresponding
   * java name. It also works if the association has already been done with
   * the same name or with an other one.
   * 
   * @param name the java name of the package
   * @param coqName the coq name of the package
   */
  public abstract void addPackage(String name, int coqName);
  
  /**
   * Associate package implementation name coqPackageName to the corresponding
   * java name. It also works if the association has already been done with
   * the same name or with an other one.
   * Calls the method {@link #addPackage(String, int)}
   * @param name the java name of the package
   * @param coqName the coq name of the package
   */
  public final void addPackage(final String name, final Pkg coqName) {
    addPackage(name, coqName.ordinal());
  }
  
  /**
   * Returns the registered package number of the package of the
   * specified Java class.
   * @param jc the class to get the package name from
   * @return the implementation number or 0 if unfound
   */
  public abstract int getCoqPackageName(JavaClass jc);
  
  /**
   * Associate a class implementation name to the corresponding java name. It
   * also works if the association has already been done with the same name or
   * with an other one.
   * 
   * @param jc the java class to add
   * @param className the Bicolano class name
   */
  public abstract void addClass(JavaClass jc, int className);
  
  /**
   * Associate a class implementation name to the corresponding java name. It
   * also works if the association has already been done with the same name or
   * with an other one.
   * Calls the methods {@link #addClass(JavaClass)}.
   * @param jc the java class to add
   * @param className the Bicolano class name
   */
  public void addClass(final JavaClass jc, final Clss className) {
    addClass(jc, className.ordinal());
  }
  
  /**
   * Associate a class implementation name to the corresponding java name. It
   * also works if the association has already been done with the same name or
   * with an other one.
   * @param jc the java class to associate to the coq name
   */
  public abstract void addClass(JavaClass jc);

  /**
   * Returns the registered class number of the
   * specified Java class.
   * @param jc the class to get the number for
   * @return the implementation number or 0 if unfound
   */
  public abstract int getCoqClassName(JavaClass jc);
  
  /**
   * Associate a field implementation name to the corresponding java name. It
   * also works if the association has already been done with the same name or
   * with an other one.
   *
   * @param javaName
   *            the corresponding human readable name
   * @param coqPackageName
   *            the Biclano package name
   * @param coqClassName
   *            the Biclano class name
   * @param coqFieldName
   *            the Biclano field name
   */
  public abstract void addField(String javaName, int coqPackageName, int coqClassName,
                       int coqFieldName);

  /**
   * Associate a method implementation name to the corresponding java name. It
   * also works if the association has already been done with the same name or
   * with an other one.
   * 
   * @param javaName
   *            the corresponding human readable name
   * @param coqPackageName
   *            the Bicolano package name
   * @param coqClassName
   *            the Bicolano class name
   * @param coqMethodName
   *            the Bicolano method name
   */
  public abstract void addMethod(String javaName, int coqPackageName,
                        int coqClassName, int coqMethodName);
  
  /**
   * Associate a method implementation name to the corresponding java name. It
   * also works if the association has already been done with the same name or
   * with an other one.
   * Basically calls the method {@link #addMethod(String, int, int, int)}.
   * 
   * @param met
   *            the method enum to add
   * @param coqPackageName
   *            the Bicolano package to add
   * @param coqClassName
   *            the Bicolano class to add
   */
  public void addMethod(final Meth met, final Pkg coqPackageName,
                        final Clss coqClassName) {
    addMethod(met.toString(), 
              coqPackageName.ordinal(),
              coqClassName.ordinal(), 
              met.toInt());
  }
  
  /**
   * Return the class name from a class number.
   * @param coqName a valid integer
   * @return the class name
   */
  public abstract String getClassName(int coqName);
  
  /**
   * Get the package name from the package number.
   * @param coqName a valid number
   * @return the package name.
   */
  public abstract String getPackageName(int coqName);
  
  /**
   * Get the method name from the method number.
   * @param coqName the method number
   * @return the method name
   */
  public abstract String getMethodName(int coqName);
  
  /**
   * Returns all the methods that were registered so far.
   * @return a list of number representing the methods
   */
  public abstract Collection<Integer> getMethods();
  
  /**
   * Retreive  the class number from the method number.
   * @param meth the method number.
   * @return the class number
   */
  public abstract int getClassFromMethod(int meth);
  
  /**
   * Retreive  the package number from the class number.
   * @param clzz the class number.
   * @return the package number
   */
  public abstract int getPackageFromClass(int clzz);

  
  /**
   * Dump the dictionnary to the given stream.
   * @param out the stream to dump to
   */
  public abstract void write(PrintStream out);


}
