package java.security;

class ProtectionDomain$1 implements java.security.PrivilegedAction {
    /*synthetic*/ final ProtectionDomain this$0;
    
    ProtectionDomain$1(/*synthetic*/ final ProtectionDomain this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        Policy p = Policy.getPolicyNoCheck();
        return p.getPermissions(this$0);
    }
}
