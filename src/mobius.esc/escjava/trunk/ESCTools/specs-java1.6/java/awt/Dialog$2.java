package java.awt;

import java.awt.event.*;
import javax.accessibility.*;
import java.security.PrivilegedAction;

class Dialog$2 implements PrivilegedAction {
    /*synthetic*/ final Dialog this$0;
    /*synthetic*/ final Runnable val$pumpEventsForHierarchy;
    
    Dialog$2(/*synthetic*/ final Dialog this$0, /*synthetic*/ final Runnable val$pumpEventsForHierarchy) {
        this.this$0 = this$0;
        this.val$pumpEventsForHierarchy = val$pumpEventsForHierarchy;
        
    }
    
    public Object run() {
        val$pumpEventsForHierarchy.run();
        return null;
    }
}
