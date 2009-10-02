package java.util.jar;

import java.io.*;
import java.util.*;
import java.util.zip.*;

class JarFile$1 implements Enumeration {
    /*synthetic*/ final JarFile this$0;
    /*synthetic*/ final Enumeration val$enum_;
    
    JarFile$1(/*synthetic*/ final JarFile this$0, /*synthetic*/ final Enumeration val$enum_) {
        this.this$0 = this$0;
        this.val$enum_ = val$enum_;
        
    }
    
    public boolean hasMoreElements() {
        return val$enum_.hasMoreElements();
    }
    
    public JarFile$JarFileEntry nextElement() {
        ZipEntry ze = (ZipEntry)(ZipEntry)val$enum_.nextElement();
        return new JarFile$JarFileEntry(this$0, ze);
    }
    
    /*synthetic public Object nextElement() {
        return this.nextElement();
    } */
}
