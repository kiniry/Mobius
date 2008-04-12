package mobius.cct.tests.mocks;

import static org.junit.Assert.fail;
import mobius.cct.certificates.Certificate;
import mobius.cct.repositories.ClassFile;
import mobius.cct.util.Version;
import mobius.cct.verifiers.CyclicDependencyException;
import mobius.cct.verifiers.Environment;
import mobius.cct.verifiers.Verifier;

/**
 * Verifier used to test cycle detection.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class CyclicVerifier implements Verifier<ClassFile> {
    @Override
    public String getCertificateType() {
      return "mobius.cct.testcert";
    }

    @Override
    public Version getMaxVersion() {
      return new Version(1, 0);
    }

    @Override
    public Version getMinVersion() {
      return new Version(0, 0);
    }

    @Override
    public String[] getSpecificationTypes(Certificate cert) {
      return new String[]{"test"};
    }

    @Override
    public boolean verify(String name, String spec, Certificate cert,
                          Environment<ClassFile> env) {
      try {
        env.verify(name, spec);
      } catch (CyclicDependencyException e) {
        return true; // :-)
      }
      fail("Cycle not detected");
      return false;
    }
}
