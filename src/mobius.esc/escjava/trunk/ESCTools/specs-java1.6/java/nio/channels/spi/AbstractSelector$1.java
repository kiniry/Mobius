package java.nio.channels.spi;

import sun.nio.ch.Interruptible;

class AbstractSelector$1 implements Interruptible {
    /*synthetic*/ final AbstractSelector this$0;
    
    AbstractSelector$1(/*synthetic*/ final AbstractSelector this$0) {
        this.this$0 = this$0;
        
    }
    
    public void interrupt() {
        this$0.wakeup();
    }
}
