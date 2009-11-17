package java.security;

import java.io.*;
import java.util.*;
import javax.crypto.SecretKey;
import javax.security.auth.callback.*;

public final class KeyStore$SecretKeyEntry implements KeyStore$Entry {
    private final SecretKey sKey;
    
    public KeyStore$SecretKeyEntry(SecretKey secretKey) {
        
        if (secretKey == null) {
            throw new NullPointerException("invalid null input");
        }
        this.sKey = secretKey;
    }
    
    public SecretKey getSecretKey() {
        return sKey;
    }
    
    public String toString() {
        return "Secret key entry with algorithm " + sKey.getAlgorithm();
    }
}
