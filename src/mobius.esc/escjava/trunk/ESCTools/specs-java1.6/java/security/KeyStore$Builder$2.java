package java.security;

import java.io.*;
import java.security.cert.CertificateException;
import java.util.*;
import javax.security.auth.callback.*;

class KeyStore$Builder$2 extends KeyStore$Builder {
    
    /*synthetic*/ static boolean access$502(KeyStore$Builder$2 x0, boolean x1) {
        return x0.getCalled = x1;
    }
    /*synthetic*/ final KeyStore$ProtectionParameter val$protection;
    /*synthetic*/ final String val$type;
    /*synthetic*/ final Provider val$provider;
    
    KeyStore$Builder$2(/*synthetic*/ final Provider val$provider, /*synthetic*/ final String val$type, /*synthetic*/ final KeyStore$ProtectionParameter val$protection) throws CertificateException, NoSuchAlgorithmException, IOException, KeyStoreException {
        this.val$provider = val$provider;
        this.val$type = val$type;
        this.val$protection = val$protection;
        
    }
    private volatile boolean getCalled;
    private final PrivilegedExceptionAction action = new KeyStore$Builder$2$1(this);
    
    public synchronized KeyStore getKeyStore() throws KeyStoreException {
        try {
            return (KeyStore)(KeyStore)AccessController.doPrivileged(action);
        } catch (PrivilegedActionException e) {
            Throwable cause = e.getCause();
            throw new KeyStoreException("KeyStore instantiation failed", cause);
        }
    }
    
    public KeyStore$ProtectionParameter getProtectionParameter(String alias) {
        if (alias == null) {
            throw new NullPointerException();
        }
        if (getCalled == false) {
            throw new IllegalStateException("getKeyStore() must be called first");
        }
        return val$protection;
    }
}
