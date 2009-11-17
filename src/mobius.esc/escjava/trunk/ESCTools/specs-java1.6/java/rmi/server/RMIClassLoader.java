package java.rmi.server;

import java.net.MalformedURLException;
import java.net.URL;
import java.util.Iterator;
import sun.misc.Service;

public class RMIClassLoader {
    
    /*synthetic*/ static RMIClassLoaderSpi access$000() {
        return initializeProvider();
    }
    private static final RMIClassLoaderSpi defaultProvider = newDefaultProviderInstance();
    private static final RMIClassLoaderSpi provider = (RMIClassLoaderSpi)(RMIClassLoaderSpi)java.security.AccessController.doPrivileged(new RMIClassLoader$1());
    
    private RMIClassLoader() {
        
    }
    
    
    public static Class loadClass(String name) throws MalformedURLException, ClassNotFoundException {
        return loadClass((String)null, name);
    }
    
    public static Class loadClass(URL codebase, String name) throws MalformedURLException, ClassNotFoundException {
        return provider.loadClass(codebase != null ? codebase.toString() : null, name, null);
    }
    
    public static Class loadClass(String codebase, String name) throws MalformedURLException, ClassNotFoundException {
        return provider.loadClass(codebase, name, null);
    }
    
    public static Class loadClass(String codebase, String name, ClassLoader defaultLoader) throws MalformedURLException, ClassNotFoundException {
        return provider.loadClass(codebase, name, defaultLoader);
    }
    
    public static Class loadProxyClass(String codebase, String[] interfaces, ClassLoader defaultLoader) throws ClassNotFoundException, MalformedURLException {
        return provider.loadProxyClass(codebase, interfaces, defaultLoader);
    }
    
    public static ClassLoader getClassLoader(String codebase) throws MalformedURLException, SecurityException {
        return provider.getClassLoader(codebase);
    }
    
    public static String getClassAnnotation(Class cl) {
        return provider.getClassAnnotation(cl);
    }
    
    public static RMIClassLoaderSpi getDefaultProviderInstance() {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPermission(new RuntimePermission("setFactory"));
        }
        return defaultProvider;
    }
    
    
    public static Object getSecurityContext(ClassLoader loader) {
        return sun.rmi.server.LoaderHandler.getSecurityContext(loader);
    }
    
    private static RMIClassLoaderSpi newDefaultProviderInstance() {
        return new RMIClassLoader$2();
    }
    
    private static RMIClassLoaderSpi initializeProvider() {
        String providerClassName = System.getProperty("java.rmi.server.RMIClassLoaderSpi");
        if (providerClassName != null) {
            if (providerClassName.equals("default")) {
                return defaultProvider;
            }
            try {
                Class providerClass = Class.forName(providerClassName, false, ClassLoader.getSystemClassLoader());
                return (RMIClassLoaderSpi)(RMIClassLoaderSpi)providerClass.newInstance();
            } catch (ClassNotFoundException e) {
                throw new NoClassDefFoundError(e.getMessage());
            } catch (IllegalAccessException e) {
                throw new IllegalAccessError(e.getMessage());
            } catch (InstantiationException e) {
                throw new InstantiationError(e.getMessage());
            } catch (ClassCastException e) {
                Error error = new LinkageError("provider class not assignable to RMIClassLoaderSpi");
                error.initCause(e);
                throw error;
            }
        }
        Iterator iter = Service.providers(RMIClassLoaderSpi.class, ClassLoader.getSystemClassLoader());
        if (iter.hasNext()) {
            try {
                return (RMIClassLoaderSpi)(RMIClassLoaderSpi)iter.next();
            } catch (ClassCastException e) {
                Error error = new LinkageError("provider class not assignable to RMIClassLoaderSpi");
                error.initCause(e);
                throw error;
            }
        }
        return defaultProvider;
    }
}
