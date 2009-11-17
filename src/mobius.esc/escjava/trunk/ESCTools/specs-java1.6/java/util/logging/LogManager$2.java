package java.util.logging;

import java.io.*;
import java.util.*;
import java.security.*;

class LogManager$2 implements PrivilegedExceptionAction {
    /*synthetic*/ final LogManager this$0;
    
    LogManager$2(/*synthetic*/ final LogManager this$0) throws IOException {
        this.this$0 = this$0;
        
    }
    
    public Object run() throws Exception {
        this$0.readConfiguration();
        return null;
    }
}
