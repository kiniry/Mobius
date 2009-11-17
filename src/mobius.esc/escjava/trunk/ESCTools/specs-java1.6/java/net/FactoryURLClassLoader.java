package java.net;

import java.net.URL;

final class FactoryURLClassLoader extends URLClassLoader {
    
    FactoryURLClassLoader(URL[] urls, ClassLoader parent) {
        super(urls, parent);
    }
    
    FactoryURLClassLoader(URL[] urls) {
        super(urls);
    }
    
    public final synchronized Class loadClass(String name, boolean resolve) throws ClassNotFoundException {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            int i = name.lastIndexOf('.');
            if (i != -1) {
                sm.checkPackageAccess(name.substring(0, i));
            }
        }
        return super.loadClass(name, resolve);
    }
}
