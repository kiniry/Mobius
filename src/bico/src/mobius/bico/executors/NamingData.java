package mobius.bico.executors;

import java.io.File;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ClassGen;

import mobius.bico.Constants;
import mobius.bico.Util;


/**
 * Datas used for naming the different files.
 * @author M. Pavlova, J. Charles (julien.charles@inria.fr)
 */
public class NamingData {
    
  /** the full class name. */
  private final String fClassName;
  
  /** the name of the package of the class. */
  private String fPackage;
  
  /** the name of the class without the package. */
  private final String fName;
  
  /** the package path. */
  private final File fPath;
  
  /** the coqified name of the class. */
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
  
  
  public NamingData(final String name) {
    fClassName = name;
    fModuleName = name;
    fPackage = "";
    fPath = new File("");
    fName = fClassName;
  
  }

  public String getPackage() {
    return fPackage;
  }

  public File getPkgDir() {
    return fPath;
  }
  
  
  public String getTypeFileName() {
    return  getTypeName() + ".v";
  }
  
  
  public String getSignatureFileName() {
    return getSignatureName() + ".v";
  }
  
  
  public String getBicoClassFileName() {
    return getBicoClassName() + ".v";
  }
  
  public String getTypeName() {
    return fModuleName + "_type";
  }
  
  
  public String getSignatureName() {
    return fModuleName + "_signature";
  }
  
  
  public String getBicoClassName() {
    return fModuleName;
  }
  
  
  
  public String getTypeModule() {
    return fModuleName + "Type";
  }
  
  public String getSignatureModule() {
    return fModuleName + "Signature";
  }
  
  
  public String getBicoClassModule() {
    return fModuleName;
  }
  
  public String getClassName() {
    return fClassName;
  }

  public File getClassFile() {
    return new File(fPath, fName + Constants.CLASS_SUFFIX);
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
