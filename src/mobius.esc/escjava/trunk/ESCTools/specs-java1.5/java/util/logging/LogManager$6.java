package java.util.logging;

import java.io.*;
import java.util.*;
import java.security.*;

class LogManager$6 implements PrivilegedAction {
    /*synthetic*/ final Logger val$parent;
    /*synthetic*/ final Logger val$logger;
    
    LogManager$6(/*synthetic*/ final Logger val$logger, /*synthetic*/ final Logger val$parent) {
        this.val$logger = val$logger;
        this.val$parent = val$parent;
        
    }
    
    public Object run() {
        val$logger.setParent(val$parent);
        return null;
    }
}
