package java.util.logging;

import java.io.*;
import java.util.*;
import java.security.*;

class LogManager$5 implements PrivilegedAction {
    /*synthetic*/ final Level val$level;
    /*synthetic*/ final Logger val$logger;
    
    LogManager$5(/*synthetic*/ final Logger val$logger, /*synthetic*/ final Level val$level) {
        this.val$logger = val$logger;
        this.val$level = val$level;
        
    }
    
    public Object run() {
        val$logger.setLevel(val$level);
        return null;
    }
}
