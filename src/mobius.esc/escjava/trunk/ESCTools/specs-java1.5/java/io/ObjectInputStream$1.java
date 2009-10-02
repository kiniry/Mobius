package java.io;

import java.security.PrivilegedAction;

class ObjectInputStream$1 implements PrivilegedAction {
    /*synthetic*/ final Class val$subcl;
    
    ObjectInputStream$1(/*synthetic*/ final Class val$subcl) {
        this.val$subcl = val$subcl;
        
    }
    
    public Object run() {
        for (Class cl = val$subcl; cl != ObjectInputStream.class; cl = cl.getSuperclass()) {
            try {
                cl.getDeclaredMethod("readUnshared", new Class[0]);
                return Boolean.FALSE;
            } catch (NoSuchMethodException ex) {
            }
            try {
                cl.getDeclaredMethod("readFields", new Class[0]);
                return Boolean.FALSE;
            } catch (NoSuchMethodException ex) {
            }
        }
        return Boolean.TRUE;
    }
}
