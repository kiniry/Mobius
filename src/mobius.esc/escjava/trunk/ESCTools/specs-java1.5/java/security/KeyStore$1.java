package java.security;

import java.io.*;
import java.util.*;
import javax.security.auth.callback.*;

class KeyStore$1 implements PrivilegedAction {
    
    KeyStore$1() {
        
    }
    
    public Object run() {
        return Security.getProperty("keystore.type");
    }
}
