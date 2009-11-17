package java.security;

import java.io.*;
import java.util.*;
import javax.security.auth.callback.*;

final class KeyStore$Builder$FileBuilder extends KeyStore$Builder {
    
    /*synthetic*/ static KeyStore$ProtectionParameter access$402(KeyStore$Builder$FileBuilder x0, KeyStore$ProtectionParameter x1) {
        return x0.protection = x1;
    }
    
    /*synthetic*/ static KeyStore$ProtectionParameter access$400(KeyStore$Builder$FileBuilder x0) {
        return x0.protection;
    }
    
    /*synthetic*/ static File access$300(KeyStore$Builder$FileBuilder x0) {
        return x0.file;
    }
    
    /*synthetic*/ static String access$200(KeyStore$Builder$FileBuilder x0) {
        return x0.type;
    }
    
    /*synthetic*/ static Provider access$100(KeyStore$Builder$FileBuilder x0) {
        return x0.provider;
    }
    private final String type;
    private final Provider provider;
    private final File file;
    private KeyStore$ProtectionParameter protection;
    private final AccessControlContext context;
    private KeyStore keyStore;
    private Throwable oldException;
    
    KeyStore$Builder$FileBuilder(String type, Provider provider, File file, KeyStore$ProtectionParameter protection, AccessControlContext context) {
        
        this.type = type;
        this.provider = provider;
        this.file = file;
        this.protection = protection;
        this.context = context;
    }
    
    public synchronized KeyStore getKeyStore() throws KeyStoreException {
        if (keyStore != null) {
            return keyStore;
        }
        if (oldException != null) {
            throw new KeyStoreException("Previous KeyStore instantiation failed", oldException);
        }
        PrivilegedExceptionAction action = new KeyStore$Builder$FileBuilder$1(this);
        try {
            keyStore = (KeyStore)(KeyStore)AccessController.doPrivileged(action, context);
            return keyStore;
        } catch (PrivilegedActionException e) {
            oldException = e.getCause();
            throw new KeyStoreException("KeyStore instantiation failed", oldException);
        }
    }
    
    public synchronized KeyStore$ProtectionParameter getProtectionParameter(String alias) {
        if (alias == null) {
            throw new NullPointerException();
        }
        if (keyStore == null) {
            throw new IllegalStateException("getKeyStore() must be called first");
        }
        return protection;
    }
}
