package java.io;

import java.security.AccessController;
import java.security.SecureRandom;
import sun.security.action.GetPropertyAction;

class File$LazyInitialization {
    
    private File$LazyInitialization() {
        
    }
    static final SecureRandom random = new SecureRandom();
    static final String temporaryDirectory = temporaryDirectory();
    
    static String temporaryDirectory() {
        return File.access$000().normalize((String)(String)AccessController.doPrivileged(new GetPropertyAction("java.io.tmpdir")));
    }
}
