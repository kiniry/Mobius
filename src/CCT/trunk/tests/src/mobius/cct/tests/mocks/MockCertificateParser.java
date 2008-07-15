package mobius.cct.tests.mocks;

import mobius.cct.certificates.CertificateParser;
import mobius.cct.certificates.CertifiedClass;
import mobius.cct.repositories.InvalidFormatException;

/**
 * Mock implementation of CertificateParser
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class MockCertificateParser implements
  CertificateParser<MockClassFile> {

  @Override
  public CertifiedClass<MockClassFile> parse(MockClassFile c)
      throws InvalidFormatException {
    return new MockCertifiedClass(c);
  }

}
