package java.security.cert;

import java.security.PrivilegedAction;
import java.security.Security;
import sun.security.jca.*;

class CertStore$1 implements PrivilegedAction {
    
    CertStore$1() {
        
    }
    
    public Object run() {
        return Security.getProperty("certstore.type");
    }
}
