package java.lang.management;

import java.security.PrivilegedAction;

class ManagementFactory$1 implements PrivilegedAction {
    /*synthetic*/ final Class val$interfaceClass;
    
    ManagementFactory$1(/*synthetic*/ final Class val$interfaceClass) {
        this.val$interfaceClass = val$interfaceClass;
        
    }
    
    public Object run() {
        return val$interfaceClass.getClassLoader();
    }
}
