package java.lang;

import java.security.PrivilegedAction;

class Thread$1 implements PrivilegedAction {
    /*synthetic*/ final Class val$subcl;
    
    Thread$1(/*synthetic*/ final Class val$subcl) {
        this.val$subcl = val$subcl;
        
    }
    
    public Object run() {
        for (Class cl = val$subcl; cl != Thread.class; cl = cl.getSuperclass()) {
            try {
                cl.getDeclaredMethod("getContextClassLoader", new Class[0]);
                return Boolean.TRUE;
            } catch (NoSuchMethodException ex) {
            }
            try {
                Class[] params = {ClassLoader.class};
                cl.getDeclaredMethod("setContextClassLoader", params);
                return Boolean.TRUE;
            } catch (NoSuchMethodException ex) {
            }
        }
        return Boolean.FALSE;
    }
}
