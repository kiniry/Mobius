package java.util.logging;

import java.io.*;
import java.security.*;

class FileHandler$InitializationErrorManager extends ErrorManager {
    
    /*synthetic*/ FileHandler$InitializationErrorManager(java.util.logging.FileHandler$1 x0) {
        this();
    }
    
    private FileHandler$InitializationErrorManager() {
        
    }
    Exception lastException;
    
    public void error(String msg, Exception ex, int code) {
        lastException = ex;
    }
}
