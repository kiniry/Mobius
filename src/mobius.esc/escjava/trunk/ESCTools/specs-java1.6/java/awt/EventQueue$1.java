package java.awt;

import java.security.PrivilegedAction;

class EventQueue$1 implements PrivilegedAction {
    /*synthetic*/ final EventQueue this$0;
    
    EventQueue$1(/*synthetic*/ final EventQueue this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        EventDispatchThread t = new EventDispatchThread(EventQueue.access$000(this$0), EventQueue.access$100(this$0), this$0);
        t.setContextClassLoader(EventQueue.access$200(this$0));
        t.setPriority(Thread.NORM_PRIORITY + 1);
        t.setDaemon(false);
        return t;
    }
}
