package java.security;

import java.lang.reflect.*;
import java.util.*;
import java.io.*;
import sun.security.jca.*;

class Security$2 implements PrivilegedAction {
    /*synthetic*/ final boolean val$pa;
    
    Security$2(/*synthetic*/ final boolean val$pa) {
        this.val$pa = val$pa;
        
    }
    
    public Object run() {
        try {
            Class cl = Class.forName("java.lang.SecurityManager", false, null);
            Field f = null;
            boolean accessible = false;
            if (val$pa) {
                f = cl.getDeclaredField("packageAccessValid");
                accessible = f.isAccessible();
                f.setAccessible(true);
            } else {
                f = cl.getDeclaredField("packageDefinitionValid");
                accessible = f.isAccessible();
                f.setAccessible(true);
            }
            f.setBoolean(f, false);
            f.setAccessible(accessible);
        } catch (Exception e1) {
        }
        return null;
    }
}
