package java.lang;

import java.security.PrivilegedAction;
import sun.reflect.annotation.*;

class Class$3 implements PrivilegedAction {
    
    Class$3() {
        
    }
    
    public Object run() {
        if (System.out == null) {
            return null;
        }
        String val = System.getProperty("sun.reflect.noCaches");
        if (val != null && val.equals("true")) {
            Class.access$202(false);
        }
        Class.access$302(true);
        return null;
    }
}
