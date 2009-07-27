package mobius.cct.classfile;

/**
 * Fully qualified name of a class.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class ClassName {
  /**
   * Package name.
   */
  private final PackageName fPackageName;
  
  /**
   * Class name.
   */
  private final String fName;
  
  /**
   * Cached hash value.
   */
  private final int fHash;
  
  /**
   * Constructor.
   * @param packageName Name of package.
   * @param name Class name.
   */
  public ClassName(final PackageName packageName, 
                   final String name) {
    if (name == null) {
      throw new IllegalArgumentException("name");
    }
    fPackageName = packageName;
    fName = name;
    fHash = internalForm().hashCode();
  }
  
  /**
   * Get class name in internal form, with slashes as separators.
   * @return Class name.
   */
  public String internalForm() {
    if (fPackageName.isRoot()) {
      return fName;
    } else {
      return fPackageName.internalForm() + "/" + fName;
    }
  }
  
  /**
   * Get class name in external form, with dots as separators.
   * @return Class name.
   */
  public String externalForm() {
    if (fPackageName.isRoot()) {
      return fName;
    } else {
      return fPackageName.externalForm() + "." + fName;
    }
  }
  
  /**
   * Parse fully qualified class name in internal form.
   * @param name Class name.
   * @return ClassName instance.
   */
  public static ClassName parseInternal(final String name) {
    final int sep = name.lastIndexOf('/');
    if (sep == -1) {
      return new ClassName(PackageName.root(), name);
    } else {
      final String n = name.substring(sep + 1);
      final String p = name.substring(0, sep);
      return new ClassName(PackageName.parseInternal(p), n);
    }
  }
  
  /**
   * Hash.
   * @return hashcode.
   */
  @Override
  public int hashCode() {
    return fHash;
  }
  
  /**
   * Get package name.
   * @return Package name.
   */
  public PackageName getPackage() {
    return fPackageName;
  }
  
  /**
   * Get class name (without package).
   * @return Class name.
   */
  public String getName() {
    return fName;
  }
  
  /**
   * Equals.
   * @param obj Object to be compared.
   * @return True iff class names are equal.
   */
  @Override
  public boolean equals(final Object obj) {
    if (obj instanceof ClassName) {
      return fHash == obj.hashCode() && 
        fName.equals(((ClassName)obj).getName()) &&
        fPackageName.equals(((ClassName)obj).getPackage()); 
    } else {
      return false;
    }
  }
}
