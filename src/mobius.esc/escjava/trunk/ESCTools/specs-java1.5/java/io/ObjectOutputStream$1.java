package java.io;

import java.security.PrivilegedAction;

class ObjectOutputStream$1 implements PrivilegedAction {
    /*synthetic*/ final Class val$subcl;
    
    ObjectOutputStream$1(/*synthetic*/ final Class val$subcl) {
        this.val$subcl = val$subcl;
        
    }
    
    public Object run() {
        for (Class cl = val$subcl; cl != ObjectOutputStream.class; cl = cl.getSuperclass()) {
            try {
                cl.getDeclaredMethod("writeUnshared", new Class[]{Object.class});
                return Boolean.FALSE;
            } catch (NoSuchMethodException ex) {
            }
            try {
                cl.getDeclaredMethod("putFields", new Class[0]);
                return Boolean.FALSE;
            } catch (NoSuchMethodException ex) {
            }
        }
        return Boolean.TRUE;
    }
}
