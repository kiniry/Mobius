package java.rmi.server;

import java.net.MalformedURLException;
import java.net.URL;


public interface LoaderHandler {
    static final String packagePrefix = "sun.rmi.server";
    
    
    Class loadClass(String name) throws MalformedURLException, ClassNotFoundException;
    
    
    Class loadClass(URL codebase, String name) throws MalformedURLException, ClassNotFoundException;
    
    
    Object getSecurityContext(ClassLoader loader);
}
