package java.beans;

import java.applet.*;
import java.awt.*;
import java.io.*;

class Beans$2 implements java.security.PrivilegedAction {
    /*synthetic*/ final String val$resourceName;
    /*synthetic*/ final ClassLoader val$cloader;
    
    Beans$2(/*synthetic*/ final ClassLoader val$cloader, /*synthetic*/ final String val$resourceName) {
        this.val$cloader = val$cloader;
        this.val$resourceName = val$resourceName;
        
    }
    
    public Object run() {
        if (val$cloader == null) return ClassLoader.getSystemResource(val$resourceName); else return val$cloader.getResource(val$resourceName);
    }
}
