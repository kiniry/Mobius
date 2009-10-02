package java.util;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.security.PrivilegedExceptionAction;
import sun.util.calendar.ZoneInfo;

class Calendar$1 implements PrivilegedExceptionAction {
    /*synthetic*/ final Calendar this$0;
    /*synthetic*/ final ObjectInputStream val$input;
    
    Calendar$1(/*synthetic*/ final Calendar this$0, /*synthetic*/ final ObjectInputStream val$input) throws ClassNotFoundException, IOException {
        this.this$0 = this$0;
        this.val$input = val$input;
        
    }
    
    public ZoneInfo run() throws Exception {
        return (ZoneInfo)(ZoneInfo)val$input.readObject();
    }
    
    /*synthetic public Object run() throws Exception {
        return this.run();
    } */
}
