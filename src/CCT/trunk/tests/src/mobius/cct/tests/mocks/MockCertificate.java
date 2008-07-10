package mobius.cct.tests.mocks;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import mobius.cct.certificates.Certificate;
import mobius.cct.util.Version;

/**
 * Certificate implementation used for tests.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class MockCertificate implements Certificate {
  /**
   * Certificate type.
   */
  private String type;
  
  public Map<String, byte[]> getMethodCerts() {
    return methodCerts;
  }

  public void setMethodCerts(Map<String, byte[]> methodCerts) {
    this.methodCerts = methodCerts;
  }

  public byte[] getClassCert() {
    return classCert;
  }

  public void setClassCert(byte[] classCert) {
    this.classCert = classCert;
  }

  public Set<String> getImports() {
    return imports;
  }

  public void setImports(Set<String> imports) {
    this.imports = imports;
  }

  public void setType(String type) {
    this.type = type;
  }

  public void setVersion(Version version) {
    this.version = version;
  }

  /**
   * Certificate version.
   */
  private Version version;
  
  /**
   * Map with method certificates.
   */
  private Map<String, byte[]> methodCerts;
  
  /**
   * Class-level certificate.
   */
  private byte[] classCert;
  
  /**
   * Imported certificates.
   */
  private Set<String> imports;
  
  /**
   * Create empty certificate with default ype and version.
   */
  public MockCertificate() {
    type = "mobius.cct.mockcert";
    version = new Version(1, 0);
    classCert = new byte[]{};
    methodCerts = new HashMap<String, byte[]>();
    imports = new HashSet<String>();
  }
  
  @Override
  public Iterator<String> getCertifiedMethods() {
    return methodCerts.keySet().iterator();
  }

  @Override
  public byte[] getClassCertificate() {
    return classCert;
  }

  @Override
  public Set<String> getImportedCerts() {
    return imports;
  }

  @Override
  public byte[] getMethodCertificate(String name) {
    return methodCerts.get(name);
  }

  @Override
  public String getType() {
    return type;
  }

  @Override
  public Version getVersion() {
    return version;
  }

}
