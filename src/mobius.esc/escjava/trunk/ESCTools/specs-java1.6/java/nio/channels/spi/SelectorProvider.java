package java.nio.channels.spi;

import java.io.IOException;
import java.nio.channels.*;
import java.security.AccessController;
import java.util.Iterator;
import sun.misc.Service;
import sun.misc.ServiceConfigurationError;

public abstract class SelectorProvider {
    
    /*synthetic*/ static boolean access$200() {
        return loadProviderAsService();
    }
    
    /*synthetic*/ static SelectorProvider access$102(SelectorProvider x0) {
        return provider = x0;
    }
    
    /*synthetic*/ static SelectorProvider access$100() {
        return provider;
    }
    
    /*synthetic*/ static boolean access$000() {
        return loadProviderFromProperty();
    }
    private static final Object lock = new Object();
    private static SelectorProvider provider = null;
    
    protected SelectorProvider() {
        
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) sm.checkPermission(new RuntimePermission("selectorProvider"));
    }
    
    private static boolean loadProviderFromProperty() {
        String cn = System.getProperty("java.nio.channels.spi.SelectorProvider");
        if (cn == null) return false;
        try {
            Class c = Class.forName(cn, true, ClassLoader.getSystemClassLoader());
            provider = (SelectorProvider)(SelectorProvider)c.newInstance();
            return true;
        } catch (ClassNotFoundException x) {
            throw new ServiceConfigurationError(x);
        } catch (IllegalAccessException x) {
            throw new ServiceConfigurationError(x);
        } catch (InstantiationException x) {
            throw new ServiceConfigurationError(x);
        } catch (SecurityException x) {
            throw new ServiceConfigurationError(x);
        }
    }
    
    private static boolean loadProviderAsService() {
        Iterator i = Service.providers(SelectorProvider.class, ClassLoader.getSystemClassLoader());
        for (; ; ) {
            try {
                if (!i.hasNext()) return false;
                provider = (SelectorProvider)(SelectorProvider)i.next();
                return true;
            } catch (ServiceConfigurationError sce) {
                if (sce.getCause() instanceof SecurityException) {
                    continue;
                }
                throw sce;
            }
        }
    }
    
    public static SelectorProvider provider() {
        synchronized (lock) {
            if (provider != null) return provider;
            return (SelectorProvider)(SelectorProvider)AccessController.doPrivileged(new SelectorProvider$1());
        }
    }
    
    public abstract DatagramChannel openDatagramChannel() throws IOException;
    
    public abstract Pipe openPipe() throws IOException;
    
    public abstract AbstractSelector openSelector() throws IOException;
    
    public abstract ServerSocketChannel openServerSocketChannel() throws IOException;
    
    public abstract SocketChannel openSocketChannel() throws IOException;
    
    public Channel inheritedChannel() throws IOException {
        return null;
    }
}
