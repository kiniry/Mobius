package mobius.bico.executors;

import java.io.File;

import mobius.bico.Util;


/**
 * 
 * @author M. Pavlova, J. Charles (julien.charles@inria.fr)
 */
public class ClassNamingData {
  
  /** the package path. */
  private final File fPath;
  
  /** the full class name. */
  private final String fClassName;
  
  /** the name of the class without the package. */
  private final String fName;
  
  /** the path + the module name. */
  private final String fBicoFileName;
  
  /** the coqified name of the class. */
  private final String fModuleName;
  
  
  public ClassNamingData(final String _clname) {
    String clname;
    if (_clname.endsWith(Constants.CLASS_SUFFIX)) {
      clname = Util.removeClassSuffix(_clname);
    } 
    else {
      clname = _clname;
    }
    fClassName = clname;
    fModuleName = Util.coqify(clname);
    fPath = computePath();
    fName = computeName();
    fBicoFileName = fPath.getPath() + File.separator + fModuleName;
  }

    
  public File getPath() {
    return fPath;
  }
  
  private File computePath() {
    String clname = fClassName;
    final int i = clname.lastIndexOf(Constants.LINUX_PATH_SEPARATOR);
    if (i != -1) {
      clname = clname.substring(0, i);
    }
    return new File(clname);
  }
  
  
  private String computeName() {
    final int i = fClassName.lastIndexOf(Constants.LINUX_PATH_SEPARATOR);
    return fClassName.substring(i + 1);
  }
  
  
  
  public String getTypeCoqFileName() {
    return  getTypeName() + ".v";
  }
  
  
  public String getSignatureCoqFileName() {
    return getSignatureName() + ".v";
  }
  
  
  public String getBicoClassCoqFileName() {
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
  
  @Override
  public String toString() {
    return fModuleName;
  }
  
  @Override
  public boolean equals (final Object o) {
    return (o instanceof ClassNamingData) && 
          ((ClassNamingData) o).fBicoFileName.equals(fBicoFileName);
  }
  
  @Override
  public int hashCode() {
    return fBicoFileName.hashCode();
  }

}
