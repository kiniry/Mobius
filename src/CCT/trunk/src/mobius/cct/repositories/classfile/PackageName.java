package mobius.cct.repositories.classfile;

/**
 * Fully qualified name of a package.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 *
 */
public final class PackageName {
  /**
   * Instance of root package.
   */
  private static final PackageName ROOT = new PackageName(null, "");
  
  /**
   * Parent package (null for root).
   */
  private final PackageName fParent;
  
  /**
   * Package name.
   */
  private final String fName;
  
  /**
   * Constructor.
   * @param parent Parent package.
   * @param name Package name.
   */
  private PackageName(final PackageName parent, 
                      final String name) {
    fParent = parent;
    fName = name;
  }
  
  /**
   * Get an instance of this class representing root package.
   * @return Root package.
   */
  public static PackageName root() {
    return ROOT;
  }
  
  /**
   * Create an instance of this class.
   * @param parent Parent package.
   * @param name Package name.
   * @return Instance representing the requested package.
   */
  public static PackageName getPackage(final PackageName parent,
                                       final String name) {
    if (name == null) {
      throw new IllegalArgumentException("name");
    }
    if (parent == null) {
      throw new IllegalArgumentException("parent");
    }
    return new PackageName(parent, name);
  }
  
  /**
   * Get parent package. Root package returns null.
   * @return Parent or null.
   */
  public PackageName getParent() {
    return fParent;
  }
  
  /**
   * Get package name. Root package returns empty string.
   * @return Package name.
   */
  public String getName() {
    return fName;
  }
  
  /**
   * Get fully qualified name in internal form (with slashes).
   * @return Package name.
   */
  public String internalForm() {
    return fqnBuilder('/').toString();
  }

  /**
   * Get fully qualified name in external form (with dots).
   * @return Package name.
   */
  public String externalForm() {
    return fqnBuilder('.').toString();
  }
  
  /**
   * Check if this is the root package.
   * @return true iff this is the root.package.
   */
  public boolean isRoot() {
    return fParent == null;
  }
  
  /**
   * Get fully qualified name as StringBuilder.
   * @param sep Package separator.
   * @return Package name.
   */
  private StringBuilder fqnBuilder(final char sep) {
    if (fParent == null) {  // root package
      return new StringBuilder();
    } else {
      final StringBuilder result = fParent.fqnBuilder(sep);
      if (fParent != ROOT) {
        result.append(sep);
      }
      result.append(fName);
      return result;
    }
  }
  
}
