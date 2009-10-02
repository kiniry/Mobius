package java.security;

import java.io.*;
import java.util.*;
import javax.security.auth.callback.*;

public class KeyStore$PasswordProtection implements KeyStore$ProtectionParameter, javax.security.auth.Destroyable {
    private final char[] password;
    private volatile boolean destroyed = false;
    
    public KeyStore$PasswordProtection(char[] password) {
        
        this.password = (password == null) ? null : (char[])(char[])password.clone();
    }
    
    public synchronized char[] getPassword() {
        if (destroyed) {
            throw new IllegalStateException("password has been cleared");
        }
        return password;
    }
    
    public synchronized void destroy() throws javax.security.auth.DestroyFailedException {
        destroyed = true;
        if (password != null) {
            Arrays.fill(password, ' ');
        }
    }
    
    public synchronized boolean isDestroyed() {
        return destroyed;
    }
}
