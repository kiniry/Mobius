package javax.xml.parsers;

import java.security.*;
import java.net.*;
import java.io.*;
import java.util.*;

class SecuritySupport {
    
    SecuritySupport() {
        
    }
    
    ClassLoader getContextClassLoader() {
        return (ClassLoader)(ClassLoader)AccessController.doPrivileged(new SecuritySupport$1(this));
    }
    
    String getSystemProperty(final String propName) {
        return (String)(String)AccessController.doPrivileged(new SecuritySupport$2(this, propName));
    }
    
    FileInputStream getFileInputStream(final File file) throws FileNotFoundException {
        try {
            return (FileInputStream)(FileInputStream)AccessController.doPrivileged(new SecuritySupport$3(this, file));
        } catch (PrivilegedActionException e) {
            throw (FileNotFoundException)(FileNotFoundException)e.getException();
        }
    }
    
    InputStream getResourceAsStream(final ClassLoader cl, final String name) {
        return (InputStream)(InputStream)AccessController.doPrivileged(new SecuritySupport$4(this, cl, name));
    }
    
    boolean doesFileExist(final File f) {
        return ((Boolean)(Boolean)AccessController.doPrivileged(new SecuritySupport$5(this, f))).booleanValue();
    }
}
