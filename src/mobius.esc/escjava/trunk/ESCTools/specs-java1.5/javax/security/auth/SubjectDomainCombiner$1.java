package javax.security.auth;

class SubjectDomainCombiner$1 implements java.security.PrivilegedAction {
    /*synthetic*/ final SubjectDomainCombiner this$0;
    /*synthetic*/ final Subject val$s;
    
    SubjectDomainCombiner$1(/*synthetic*/ final SubjectDomainCombiner this$0, /*synthetic*/ final Subject val$s) {
        this.this$0 = this$0;
        this.val$s = val$s;
        
    }
    
    public Object run() {
        SubjectDomainCombiner.access$100().println(val$s.toString());
        return null;
    }
}
