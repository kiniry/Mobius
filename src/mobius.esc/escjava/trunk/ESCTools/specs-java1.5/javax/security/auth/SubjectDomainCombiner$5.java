package javax.security.auth;

import java.security.PrivilegedAction;

class SubjectDomainCombiner$5 implements PrivilegedAction {
    
    SubjectDomainCombiner$5() {
        
    }
    
    public Object run() {
        return javax.security.auth.Policy.getPolicy();
    }
}
