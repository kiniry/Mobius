package java.lang;

import java.io.*;
import sun.nio.ch.Interruptible;
import sun.reflect.annotation.AnnotationType;

class System$2 implements sun.misc.JavaLangAccess {
    
    System$2() {
        
    }
    
    public sun.reflect.ConstantPool getConstantPool(Class klass) {
        return klass.getConstantPool();
    }
    
    public void setAnnotationType(Class klass, AnnotationType type) {
        klass.setAnnotationType(type);
    }
    
    public AnnotationType getAnnotationType(Class klass) {
        return klass.getAnnotationType();
    }
    
    public void blockedOn(Thread t, Interruptible b) {
        t.blockedOn(b);
    }
}
