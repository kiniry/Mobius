package java.lang;

import java.lang.reflect.Constructor;
import java.security.PrivilegedExceptionAction;

class SystemClassLoaderAction implements PrivilegedExceptionAction {
    private ClassLoader parent;
    
    SystemClassLoaderAction(ClassLoader parent) {
        
        this.parent = parent;
    }
    
    public Object run() throws Exception {
        ClassLoader sys;
        Constructor ctor;
        Class c;
        Class[] cp = {ClassLoader.class};
        Object[] params = {parent};
        String cls = System.getProperty("java.system.class.loader");
        if (cls == null) {
            return parent;
        }
        c = Class.forName(cls, true, parent);
        ctor = c.getDeclaredConstructor(cp);
        sys = (ClassLoader)(ClassLoader)ctor.newInstance(params);
        Thread.currentThread().setContextClassLoader(sys);
        return sys;
    }
}
