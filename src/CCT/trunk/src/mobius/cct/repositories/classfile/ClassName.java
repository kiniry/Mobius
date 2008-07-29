package mobius.cct.repositories.classfile;

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
   * Constructor.
   * @param packageName Name of package, with slashes as separators.
   * @param name Class name.
   */
  public ClassName(final PackageName packageName, 
                   final String name) {
    if (name == null) {
      throw new IllegalArgumentException("name");
    }
    fPackageName = packageName;
    fName = name;
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
    final int sep = name.indexOf('/');
    if (sep == -1) {
      return new ClassName(PackageName.root(), name);
    } else {
      final String n = name.substring(sep + 1);
      final String p = name.substring(0, sep);
      return new ClassName(PackageName.parseInternal(p), n);
    }
  }
}
