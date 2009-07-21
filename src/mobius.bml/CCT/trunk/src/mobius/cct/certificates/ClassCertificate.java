package mobius.cct.certificates;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import mobius.cct.util.ArrayIterator;
import mobius.cct.util.Version;

/**
 * Class certificate (without method certificates).
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class ClassCertificate extends Certificate {
  /**
   * Attribute name.
   */
  public static final String ATTR = "mobius.PCCCert";
  
  /**
   * Imported certificates.
   */
  private final String[] fImports;
  
  /**
   * Constructor.   
   * @param type Certificate type.
   * @param version Certificate version.
   * @param imports Array of imported certificates.
   * @param data Certificate data.
   */
  public ClassCertificate(final String type,
                          final Version version,
                          final String[] imports,
                          final byte[] data) {
    super(type, version, data);
    fImports = new String[imports.length];
    for (int i = 0; i < imports.length; i++) {
      fImports[i] = imports[i];
    }
  }
  
  /**
   * Merge with another class certificate.
   * Data sections are concatenated, import lists
   * are sorted and merged.
   * @param c Class certificate.
   * @return Merged certificate.
   */
  public ClassCertificate merge(final ClassCertificate c) {
    final byte[] data1 = getData();
    final byte[] data2 = c.getData();
    final byte[] data = 
      new byte[data1.length + data2.length];
    for (int i = 0; i < data1.length; i++) {
      data[i] = data1[i];
    }
    for (int i = 0; i < data2.length; i++) {
      data[data1.length + i] = data2[i];
    }
    final String[] imports = 
      mergeImports(getImports(), c.getImports());
    return 
      new ClassCertificate(getType(), getVersion(), imports, data);
  }

  /**
   * Merge import lists.
   * @param i1 First import list.
   * @param i2 Second import list.
   * @return Merged list.
   */
  private static String[] mergeImports(final Iterator<String> i1,
                                       final Iterator<String> i2) {
    final Set<String> imports = new HashSet<String>();
    while (i1.hasNext()) {
      imports.add(i1.next());
    }
    while (i2.hasNext()) {
      imports.add(i2.next());
    }
    return imports.toArray(new String[]{});
  }
  
  /**
   * Get number of imported certificates.
   * @return Number of imported certificates.
   */
  public int getImportCount() {
    return fImports.length;
  }
  
  /**
   * Get imported certificates.
   * @return Iterator.
   */
  public Iterator<String> getImports() {
    return new ArrayIterator<String>(fImports);
  }
}
