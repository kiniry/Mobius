package mobius.cct.classfile;

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
   * Cached hash value.
   */
  private final int fHash;
  
  /**
   * Constructor.
   * @param parent Parent package.
   * @param name Package name.
   */
  private PackageName(final PackageName parent, 
                      final String name) {
    fParent = parent;
    fName = name;
    fHash = internalForm().hashCode();
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
  
  /**
   * Parse package name in internal form.
   * @param name Package name. Root package = empty string.
   * @return Package name.
   */
  public static PackageName parseInternal(final String name) {
    final int sep = name.lastIndexOf('/');
    if (sep == -1) {
      if (name.equals("")) {
        return root();
      } else {
        return getPackage(root(), name);
      }
    } else {
      final String n = name.substring(sep + 1);
      final String p = name.substring(0, sep);
      return getPackage(parseInternal(p), n);
    }
  }
  
  /**
   * Hashcode.
   * @return Hash code.
   */
  @Override
  public int hashCode() {
    return fHash;
  }
  
  /**
   * Compare package names.
   * @param obj Object to compare.
   * @return True iff objects are equal.
   */
  @Override
  public boolean equals(final Object obj) {
    if (obj instanceof PackageName) {
      return internalForm().equals(((PackageName)obj).internalForm());
    } else {
      return false;
    }
  }
}
