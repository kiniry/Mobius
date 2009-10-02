package javax.security.auth;

import java.security.PrivilegedAction;

class SubjectDomainCombiner$3 implements PrivilegedAction {
    /*synthetic*/ final SubjectDomainCombiner this$0;
    /*synthetic*/ final .java.security.CodeSource val$finalCs;
    /*synthetic*/ final Subject val$finalS;
    
    SubjectDomainCombiner$3(/*synthetic*/ final SubjectDomainCombiner this$0, /*synthetic*/ final Subject val$finalS, /*synthetic*/ final .java.security.CodeSource val$finalCs) {
        this.this$0 = this$0;
        this.val$finalS = val$finalS;
        this.val$finalCs = val$finalCs;
        
    }
    
    public Object run() {
        return javax.security.auth.Policy.getPolicy().getPermissions(val$finalS, val$finalCs);
    }
}
