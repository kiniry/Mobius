package mobius.cct.tests.mocks;

import static org.junit.Assert.fail;
import mobius.cct.certificates.CertificatePack;
import mobius.cct.classfile.ClassName;
import mobius.cct.util.Version;
import mobius.cct.verifiers.CyclicDependencyException;
import mobius.cct.verifiers.Environment;
import mobius.cct.verifiers.VerificationException;
import mobius.cct.verifiers.Verifier;

/**
 * Verifier used to test cycle detection.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class CyclicVerifier implements Verifier<MockRepoClass> {
    public String getCertificateType() {
      return "mobius.cct.testcert";
    }

    public String getSpecificationType() {
      return "mobius.cct.testspec";
    }
    
    public Version getMaxVersion() {
      return new Version(1, 0);
    }

    public Version getMinVersion() {
      return new Version(0, 0);
    }

    public boolean verify(ClassName name, String spec, 
                          CertificatePack cert,
                          Environment<MockRepoClass> env) {
      try {
        env.verify(name, spec);
      } catch (CyclicDependencyException e) {
        return true; // :-)
      } catch (VerificationException e) {
        fail("Invalid exception thrown.");
      }
      fail("Cycle not detected");
      return false;
    }

}
