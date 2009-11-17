package java.awt.datatransfer;

import java.io.*;
import java.nio.*;
import java.util.*;

class DataFlavor$1 implements java.security.PrivilegedAction {
    
    DataFlavor$1() {
        
    }
    
    public Object run() {
        ClassLoader cl = Thread.currentThread().getContextClassLoader();
        return (cl != null) ? cl : ClassLoader.getSystemClassLoader();
    }
}
