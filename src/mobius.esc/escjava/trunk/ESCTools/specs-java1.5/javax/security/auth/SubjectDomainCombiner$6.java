package javax.security.auth;

import java.security.PrivilegedAction;
import java.security.ProtectionDomain;

class SubjectDomainCombiner$6 implements PrivilegedAction {
    /*synthetic*/ final ProtectionDomain val$pd;
    
    SubjectDomainCombiner$6(/*synthetic*/ final ProtectionDomain val$pd) {
        this.val$pd = val$pd;
        
    }
    
    public Object run() {
        return val$pd.toString();
    }
}
