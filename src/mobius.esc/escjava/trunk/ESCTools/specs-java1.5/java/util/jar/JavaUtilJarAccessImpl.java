package java.util.jar;

import java.io.IOException;
import sun.misc.JavaUtilJarAccess;

class JavaUtilJarAccessImpl implements JavaUtilJarAccess {
    
    JavaUtilJarAccessImpl() {
        
    }
    
    public boolean jarFileHasClassPathAttribute(JarFile jar) throws IOException {
        return jar.hasClassPathAttribute();
    }
}
