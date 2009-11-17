package java.beans;

import java.security.PrivilegedAction;

class Introspector$1 implements PrivilegedAction {
    /*synthetic*/ final Class val$fclz;
    
    Introspector$1(/*synthetic*/ final Class val$fclz) {
        this.val$fclz = val$fclz;
        
    }
    
    public Object run() {
        return val$fclz.getDeclaredMethods();
    }
}
