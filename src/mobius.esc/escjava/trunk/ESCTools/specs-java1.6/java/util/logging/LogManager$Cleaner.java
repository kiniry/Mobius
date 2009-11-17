package java.util.logging;

import java.io.*;
import java.util.*;
import java.security.*;

class LogManager$Cleaner extends Thread {
    
    /*synthetic*/ LogManager$Cleaner(LogManager x0, java.util.logging.LogManager$1 x1) {
        this(x0);
    }
    /*synthetic*/ final LogManager this$0;
    
    private LogManager$Cleaner(/*synthetic*/ final LogManager this$0) {
        this.this$0 = this$0;
        
    }
    
    public void run() {
        LogManager mgr = LogManager.access$000();
        synchronized (this$0) {
            LogManager.access$302(this$0, true);
            LogManager.access$402(this$0, true);
        }
        this$0.reset();
    }
}
