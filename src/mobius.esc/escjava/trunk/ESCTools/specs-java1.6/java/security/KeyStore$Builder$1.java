package java.security;

import java.io.*;
import java.util.*;
import javax.security.auth.callback.*;

class KeyStore$Builder$1 extends KeyStore$Builder {
    /*synthetic*/ final KeyStore$ProtectionParameter val$protectionParameter;
    /*synthetic*/ final KeyStore val$keyStore;
    
    KeyStore$Builder$1(/*synthetic*/ final KeyStore val$keyStore, /*synthetic*/ final KeyStore$ProtectionParameter val$protectionParameter) {
        this.val$keyStore = val$keyStore;
        this.val$protectionParameter = val$protectionParameter;
        
    }
    private volatile boolean getCalled;
    
    public KeyStore getKeyStore() {
        getCalled = true;
        return val$keyStore;
    }
    
    public KeyStore$ProtectionParameter getProtectionParameter(String alias) {
        if (alias == null) {
            throw new NullPointerException();
        }
        if (getCalled == false) {
            throw new IllegalStateException("getKeyStore() must be called first");
        }
        return val$protectionParameter;
    }
}
