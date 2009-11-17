package java.beans;

import java.applet.*;
import java.awt.*;
import java.io.*;

class Beans$1 implements java.security.PrivilegedAction {
    /*synthetic*/ final String val$serName;
    /*synthetic*/ final ClassLoader val$loader;
    
    Beans$1(/*synthetic*/ final ClassLoader val$loader, /*synthetic*/ final String val$serName) {
        this.val$loader = val$loader;
        this.val$serName = val$serName;
        
    }
    
    public Object run() {
        if (val$loader == null) return ClassLoader.getSystemResourceAsStream(val$serName); else return val$loader.getResourceAsStream(val$serName);
    }
}
