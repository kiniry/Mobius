package java.security.cert;

import java.security.PrivilegedAction;
import java.security.Security;
import sun.security.jca.*;

class CertPathBuilder$1 implements PrivilegedAction {
    
    CertPathBuilder$1() {
        
    }
    
    public Object run() {
        return Security.getProperty("certpathbuilder.type");
    }
}
