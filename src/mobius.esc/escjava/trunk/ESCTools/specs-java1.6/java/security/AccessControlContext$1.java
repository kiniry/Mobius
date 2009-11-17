package java.security;

import sun.security.util.Debug;

class AccessControlContext$1 implements PrivilegedAction {
    /*synthetic*/ final AccessControlContext this$0;
    /*synthetic*/ final ProtectionDomain val$pd;
    /*synthetic*/ final Debug val$db;
    
    AccessControlContext$1(/*synthetic*/ final AccessControlContext this$0, /*synthetic*/ final Debug val$db, /*synthetic*/ final ProtectionDomain val$pd) {
        this.this$0 = this$0;
        this.val$db = val$db;
        this.val$pd = val$pd;
        
    }
    
    public Object run() {
        val$db.println("domain that failed " + val$pd);
        return null;
    }
}
