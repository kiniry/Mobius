package java.security.cert;

import java.security.PrivilegedAction;
import java.security.Security;
import sun.security.jca.*;

class CertPathValidator$1 implements PrivilegedAction {
    
    CertPathValidator$1() {
        
    }
    
    public Object run() {
        return Security.getProperty("certpathvalidator.type");
    }
}
