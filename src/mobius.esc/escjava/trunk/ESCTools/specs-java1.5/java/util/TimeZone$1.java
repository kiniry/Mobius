package java.util;

import java.security.PrivilegedAction;

class TimeZone$1 implements PrivilegedAction {
    /*synthetic*/ final String val$id;
    
    TimeZone$1(/*synthetic*/ final String val$id) {
        this.val$id = val$id;
        
    }
    
    public Object run() {
        System.setProperty("user.timezone", val$id);
        return null;
    }
}
