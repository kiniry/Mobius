package java.rmi.server;

import java.io.*;
import java.net.*;

public abstract class RMISocketFactory implements RMIClientSocketFactory, RMIServerSocketFactory {
    private static RMISocketFactory factory = null;
    private static RMISocketFactory defaultSocketFactory;
    private static RMIFailureHandler handler = null;
    
    public RMISocketFactory() {
        
    }
    
    public abstract Socket createSocket(String host, int port) throws IOException;
    
    public abstract ServerSocket createServerSocket(int port) throws IOException;
    
    public static synchronized void setSocketFactory(RMISocketFactory fac) throws IOException {
        if (factory != null) {
            throw new SocketException("factory already defined");
        }
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkSetFactory();
        }
        factory = fac;
    }
    
    public static synchronized RMISocketFactory getSocketFactory() {
        return factory;
    }
    
    public static synchronized RMISocketFactory getDefaultSocketFactory() {
        if (defaultSocketFactory == null) {
            defaultSocketFactory = new sun.rmi.transport.proxy.RMIMasterSocketFactory();
        }
        return defaultSocketFactory;
    }
    
    public static synchronized void setFailureHandler(RMIFailureHandler fh) {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkSetFactory();
        }
        handler = fh;
    }
    
    public static synchronized RMIFailureHandler getFailureHandler() {
        return handler;
    }
}
