package mobius.bico.dico;

import java.io.PrintStream;

import org.apache.bcel.classfile.JavaClass;


/**
 * The dictonary creates a dictonary that can then be used to translate the
 * generated name into human-readable names.
 * 
 * @author Laurent.Hubert@irisa.fr
 */
public interface Dictionary {

  /** determine the span of the 'reserved' class names number default is 20. */
  int RESERVED_CLASSES = 20;

  /**
   * Associate package implementation name coqPackageName to the corresponding
   * java name. It also works if the association has already been done with
   * the same name or with an other one.
   * 
   * @param name the java name of the package
   * @param coqName the coq name of the package
   */
  void addPackage(String name, int coqName);

  
  /**
   * Returns the registered package number of the package of the
   * specified Java class.
   * @param jc the class to get the package name from
   * @return the implementation number or 0 if unfound
   */
  int getCoqPackageName(JavaClass jc);
  
  /**
   * Associate a class implementation name to the corresponding java name. It
   * also works if the association has already been done with the same name or
   * with an other one.
   * 
   * @param className
   *            the corresponding human readable name
   * @param packageName
   *            the Biclano package name
   * @param coqClassName
   *            the Bicolano class name
   */
  void addClass(String className, String packageName, int coqClassName);

  /**
   * Associate a class implementation name to the corresponding java name. It
   * also works if the association has already been done with the same name or
   * with an other one.
   * @param jc the java class to associate to the coq name
   */
  void addClass(JavaClass jc);

  /**
   * Returns the registered class number of the
   * specified Java class.
   * @param jc the class to get the number for
   * @return the implementation number or 0 if unfound
   */
  int getCoqClassName(JavaClass jc);
  
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
  void addField(String javaName, int coqPackageName, int coqClassName,
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
  void addMethod(String javaName, int coqPackageName,
                        int coqClassName, int coqMethodName);
  
  /**
   * Dump the dictionnary to the given stream.
   * @param out the stream to dump to
   */
  void write(PrintStream out);


}
