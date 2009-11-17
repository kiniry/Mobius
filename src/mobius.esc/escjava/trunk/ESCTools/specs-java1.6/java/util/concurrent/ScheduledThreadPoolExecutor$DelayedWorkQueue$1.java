package java.util.concurrent;

import java.util.concurrent.atomic.*;
import java.util.*;

class ScheduledThreadPoolExecutor$DelayedWorkQueue$1 implements Iterator {
    /*synthetic*/ final ScheduledThreadPoolExecutor$DelayedWorkQueue this$0;
    
    ScheduledThreadPoolExecutor$DelayedWorkQueue$1(/*synthetic*/ final ScheduledThreadPoolExecutor$DelayedWorkQueue this$0) {
        this.this$0 = this$0;
        
    }
    private Iterator it = ScheduledThreadPoolExecutor.DelayedWorkQueue.access$500(this$0).iterator();
    
    public boolean hasNext() {
        return it.hasNext();
    }
    
    public Runnable next() {
        return (Runnable)it.next();
    }
    
    public void remove() {
        it.remove();
    }
    
    /*synthetic public Object next() {
        return this.next();
    } */
}
