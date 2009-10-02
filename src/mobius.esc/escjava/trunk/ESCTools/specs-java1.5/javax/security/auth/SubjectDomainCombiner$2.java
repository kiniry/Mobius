package javax.security.auth;

import java.security.PrivilegedAction;

class SubjectDomainCombiner$2 implements PrivilegedAction {
    /*synthetic*/ final SubjectDomainCombiner this$0;
    
    SubjectDomainCombiner$2(/*synthetic*/ final SubjectDomainCombiner this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        javax.security.auth.Policy.getPolicy().refresh();
        return null;
    }
}
