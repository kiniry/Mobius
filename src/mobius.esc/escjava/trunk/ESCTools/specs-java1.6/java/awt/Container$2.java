package java.awt;

import javax.accessibility.*;

class Container$2 implements Runnable {
    /*synthetic*/ final Container this$0;
    /*synthetic*/ final Container val$nativeContainer;
    
    Container$2(/*synthetic*/ final Container this$0, /*synthetic*/ final Container val$nativeContainer) {
        this.this$0 = this$0;
        this.val$nativeContainer = val$nativeContainer;
        
    }
    
    public void run() {
        EventDispatchThread dispatchThread = (EventDispatchThread)(EventDispatchThread)Thread.currentThread();
        dispatchThread.pumpEventsForHierarchy(new Container$2$1(this), this$0);
    }
}
