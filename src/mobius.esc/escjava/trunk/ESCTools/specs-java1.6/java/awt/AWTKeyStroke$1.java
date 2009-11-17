package java.awt;

import java.security.PrivilegedAction;
import java.lang.reflect.Constructor;

class AWTKeyStroke$1 implements PrivilegedAction {
    /*synthetic*/ final Class val$clazz;
    
    AWTKeyStroke$1(/*synthetic*/ final Class val$clazz) {
        this.val$clazz = val$clazz;
        
    }
    
    public Object run() {
        try {
            Constructor ctor = val$clazz.getDeclaredConstructor(null);
            if (ctor != null) {
                ctor.setAccessible(true);
            }
            return ctor;
        } catch (SecurityException e) {
        } catch (NoSuchMethodException e) {
        }
        return null;
    }
}
