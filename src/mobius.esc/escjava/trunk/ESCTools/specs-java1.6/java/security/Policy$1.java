package java.security;

import java.io.*;
import java.lang.reflect.*;

class Policy$1 implements PrivilegedAction {
    
    Policy$1() {
        
    }
    
    public Object run() {
        return Security.getProperty("policy.provider");
    }
}
