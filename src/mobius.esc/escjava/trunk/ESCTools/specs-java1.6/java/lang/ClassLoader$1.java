package java.lang;

import java.security.PrivilegedAction;

class ClassLoader$1 implements PrivilegedAction {
    /*synthetic*/ final ClassLoader this$0;
    /*synthetic*/ final int val$i;
    /*synthetic*/ final String val$name;
    /*synthetic*/ final SecurityManager val$sm;
    
    ClassLoader$1(/*synthetic*/ final ClassLoader this$0, /*synthetic*/ final SecurityManager val$sm, /*synthetic*/ final String val$name, /*synthetic*/ final int val$i) {
        this.this$0 = this$0;
        this.val$sm = val$sm;
        this.val$name = val$name;
        this.val$i = val$i;
        
    }
    
    public Object run() {
        val$sm.checkPackageAccess(val$name.substring(0, val$i));
        return null;
    }
}
