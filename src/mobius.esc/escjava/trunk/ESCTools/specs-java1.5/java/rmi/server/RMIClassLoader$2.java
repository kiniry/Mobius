package java.rmi.server;

import java.net.MalformedURLException;

class RMIClassLoader$2 extends RMIClassLoaderSpi {
    
    RMIClassLoader$2() throws ClassNotFoundException, MalformedURLException {
        
    }
    
    public Class loadClass(String codebase, String name, ClassLoader defaultLoader) throws MalformedURLException, ClassNotFoundException {
        return sun.rmi.server.LoaderHandler.loadClass(codebase, name, defaultLoader);
    }
    
    public Class loadProxyClass(String codebase, String[] interfaces, ClassLoader defaultLoader) throws MalformedURLException, ClassNotFoundException {
        return sun.rmi.server.LoaderHandler.loadProxyClass(codebase, interfaces, defaultLoader);
    }
    
    public ClassLoader getClassLoader(String codebase) throws MalformedURLException {
        return sun.rmi.server.LoaderHandler.getClassLoader(codebase);
    }
    
    public String getClassAnnotation(Class cl) {
        return sun.rmi.server.LoaderHandler.getClassAnnotation(cl);
    }
}
