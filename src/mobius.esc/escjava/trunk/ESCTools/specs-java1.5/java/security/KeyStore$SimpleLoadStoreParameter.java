package java.security;

import java.io.*;
import java.util.*;
import javax.security.auth.callback.*;

class KeyStore$SimpleLoadStoreParameter implements KeyStore$LoadStoreParameter {
    private final KeyStore$ProtectionParameter protection;
    
    KeyStore$SimpleLoadStoreParameter(KeyStore$ProtectionParameter protection) {
        
        this.protection = protection;
    }
    
    public KeyStore$ProtectionParameter getProtectionParameter() {
        return protection;
    }
}
