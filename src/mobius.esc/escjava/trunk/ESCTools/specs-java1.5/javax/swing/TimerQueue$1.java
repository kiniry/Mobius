package javax.swing;

import java.util.*;

class TimerQueue$1 implements java.security.PrivilegedAction {
    /*synthetic*/ final TimerQueue this$0;
    /*synthetic*/ final ThreadGroup val$threadGroup;
    
    TimerQueue$1(/*synthetic*/ final TimerQueue this$0, /*synthetic*/ final ThreadGroup val$threadGroup) {
        this.this$0 = this$0;
        this.val$threadGroup = val$threadGroup;
        
    }
    
    public Object run() {
        Thread timerThread = new Thread(val$threadGroup, this$0, "TimerQueue");
        timerThread.setDaemon(true);
        timerThread.setPriority(Thread.NORM_PRIORITY);
        timerThread.start();
        return null;
    }
}
