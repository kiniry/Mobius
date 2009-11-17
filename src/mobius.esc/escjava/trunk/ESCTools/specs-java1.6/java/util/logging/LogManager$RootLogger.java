package java.util.logging;

import java.io.*;
import java.util.*;
import java.security.*;

class LogManager$RootLogger extends Logger {
    
    /*synthetic*/ LogManager$RootLogger(LogManager x0, java.util.logging.LogManager$1 x1) {
        this(x0);
    }
    /*synthetic*/ final LogManager this$0;
    
    private LogManager$RootLogger(/*synthetic*/ final LogManager this$0) {
        super("", null);
        this.this$0 = this$0;
	setLevel(LogManager.access$800());
    }
    
    public void log(LogRecord record) {
        LogManager.access$900(this$0);
        super.log(record);
    }
    
    public void addHandler(Handler h) {
        LogManager.access$900(this$0);
        super.addHandler(h);
    }
    
    public void removeHandler(Handler h) {
        LogManager.access$900(this$0);
        super.removeHandler(h);
    }
    
    public Handler[] getHandlers() {
        LogManager.access$900(this$0);
        return super.getHandlers();
    }
}
