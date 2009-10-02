package java.awt;

import java.awt.event.*;
import javax.accessibility.*;

class Dialog$1 implements Runnable {
    /*synthetic*/ final Dialog this$0;
    
    Dialog$1(/*synthetic*/ final Dialog this$0) {
        this.this$0 = this$0;
        
    }
    
    public void run() {
        EventDispatchThread dispatchThread = (EventDispatchThread)(EventDispatchThread)Thread.currentThread();
        dispatchThread.pumpEventsForHierarchy(new Dialog$1$1(this), this$0);
    }
}
