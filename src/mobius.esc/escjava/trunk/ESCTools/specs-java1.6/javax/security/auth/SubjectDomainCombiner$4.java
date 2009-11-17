package javax.security.auth;

import java.security.PrivilegedAction;

class SubjectDomainCombiner$4 implements PrivilegedAction {
    
    SubjectDomainCombiner$4() {
        
    }
    
    public Object run() {
        return java.security.Security.getProperty("cache.auth.policy");
    }
}
