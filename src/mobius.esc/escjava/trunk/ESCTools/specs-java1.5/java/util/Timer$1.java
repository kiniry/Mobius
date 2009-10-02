package java.util;

class Timer$1 extends Object {
    /*synthetic*/ final Timer this$0;
    
    Timer$1(/*synthetic*/ final Timer this$0) {
        this.this$0 = this$0;
        
    }
    
    protected void finalize() throws Throwable {
        synchronized (Timer.access$000(this$0)) {
            Timer.access$100(this$0).newTasksMayBeScheduled = false;
            Timer.access$000(this$0).notify();
        }
    }
}
