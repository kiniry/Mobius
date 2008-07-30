package mobius.bico.executors;

import java.io.File;

import mobius.bico.Util;
import mobius.bico.Constants.Suffix;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ClassGen;


/**
 * Datas used for naming the different files.
 * For all the examples for documenting the methods, a class name <code>C</code> in a package 
 * <code>a.b</code> will be used.
 * 
 * @author M. Pavlova, J. Charles (julien.charles@inria.fr)
 */
public class NamingData {
    
  /** the full class name it has the form: a.b.C . */
  private final String fClassName;
  
  /** the name of the package of the class it has the form: a.b . */
  private String fPackage;
  
  /** the name of the class without the package it has the form: C . */
  private final String fName;
  
  /** the package path it has the form: a/b/ . */
  private final File fPath;
  
  /** the coqified name of the class it has the form: a_b_C . */
  private final String fModuleName;


  /**
   * Get the informations from a Class generator.
   * @param cg the class with which to initialize the data structure
   */
  public NamingData(final ClassGen cg) {
    this(cg.getJavaClass());
  }

  /**
   * Get the informations from a JavaClass.
   * @param jc the class with which to initialize the data structure
   */
  public NamingData(final JavaClass jc) {
    fClassName = jc.getClassName();
    fModuleName = Util.coqify(fClassName);
    fPackage = jc.getPackageName();
    fPath = new File(fPackage.replace('.', File.separatorChar));
    fName = fClassName.substring(fClassName.lastIndexOf('.') + 1);
  }
  
  /**
   * Initialize the naming data structure from a given name.
   * @param name the classname as well as the module name.
   * It is considered to have no package name
   */
  public NamingData(final String name) {
    assert (name != null);
    fClassName = name;
    fModuleName = name;
    fPackage = "";
    fPath = new File("");
    fName = fClassName;
  
  }

  /**
   * A copy constructor.
   * @param data the naming data to copy.
   */
  public NamingData(final NamingData data) {
    fClassName = data.fClassName;
    fModuleName = data.fModuleName;
    fPackage = data.fPackage;
    fPath = data.fPath;
    fName = data.fName;
  }

  /**
   * Returns the package name. It has the form: <code>a.b</code>
   * @return a valid package string or an empty string for the default
   * package
   */
  public String getPackage() {
    return fPackage;
  }
  
  /**
   * Returns the package directory. It has the form: <code>a/b</code>
   * @return returns the package directory
   */
  public File getPkgDir() {
    return fPath;
  }
  
  /**
   * Returns the module name. It has the form <code>a_b_C</code>
   * @return the full module name (coqified package name + class name)
   */
  public String getModuleName() {
    return fModuleName;
  }
  
  /**
   * Returns the class name. It has the form <code>a.b.C</code>
   * @return a valid class name
   */
  public String getClassName() {
    return fClassName;
  }
  
  /**
   * The type module file name (without the extension). 
   * Looks like: <code>a_b_C_type</code>
   * @return a string representing the type 
   */
  public String getTypeName() {
    return fModuleName + "_type";
  }
  
  /**
   * The signature module file name (without the extension). 
   * Looks like: <code>a_b_C_signature</code>
   * @return a string representing the signature 
   */
  public String getSignatureName() {
    return fModuleName + "_signature";
  }
  
  /**
   * The type module name.
   * Looks like: <code>a_b_CType</code>
   * @return a string representing the type module 
   */
  public String getTypeModule() {
    return fModuleName + "Type";
  }
  
  /**
   * The signature module name.
   * Looks like: <code>a_b_CSignature</code>
   * @return a string representing the signature module 
   */
  public String getSignatureModule() {
    return fModuleName + "Signature";
  }
  
  /**
   * The type module file name (with the extension). 
   * Looks like: <code>a_b_C_type.v</code>
   * @return a string representing the type file
   */
  public String getTypeFileName() {
    return  getTypeName() + ".v";
  }
  
  /**
   * The signature module file name (with the extension). 
   * Looks like: <code>a_b_C_signature.v</code>
   * @return a string representing the signature file 
   */
  public String getSignatureFileName() {
    return getSignatureName() + ".v";
  }
  
  /**
   * The main module file name (with the extension). 
   * Looks like: <code>a_b_C.v</code>
   * @return a string representing the main module file 
   */
  public String getBicoClassFileName() {
    return getModuleName() + ".v";
  }
  

  

  /**
   * Returns the path of the class file constructed from
   * the path, the name of the class and the class suffix.
   * @return an existing file (most likely)
   */
  public File getClassFile() {
    return new File(fPath, fName + Suffix.CLASS);
  }
  
  /**
   * @return "Class Naming Data: ClassName"
   */
  @Override
  public String toString() {
    return "Class Naming Data: " + fClassName;
  }
  
  /**
   * @param o an object.
   * @return true if the 2 data structures represents the same class
   */
  @Override
  public boolean equals (final Object o) {
    if (o == null) {
      return false;
    }
    return (o instanceof NamingData) && 
          ((NamingData) o).fClassName.equals(fClassName);
  }
  
  /**
   * @return a number representing the class name
   */
  @Override
  public int hashCode() {
    return fClassName.hashCode();
  }

}
