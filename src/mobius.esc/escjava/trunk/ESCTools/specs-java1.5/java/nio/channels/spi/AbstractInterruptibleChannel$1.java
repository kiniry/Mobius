package java.nio.channels.spi;

import java.io.IOException;
import java.nio.channels.*;
import sun.nio.ch.Interruptible;

class AbstractInterruptibleChannel$1 implements Interruptible {
    /*synthetic*/ final AbstractInterruptibleChannel this$0;
    
    AbstractInterruptibleChannel$1(/*synthetic*/ final AbstractInterruptibleChannel this$0) {
        this.this$0 = this$0;
        
    }
    
    public void interrupt() {
        synchronized (AbstractInterruptibleChannel.access$000(this$0)) {
            if (!AbstractInterruptibleChannel.access$100(this$0)) return;
            AbstractInterruptibleChannel.access$202(this$0, true);
            AbstractInterruptibleChannel.access$102(this$0, false);
            try {
                this$0.implCloseChannel();
            } catch (IOException x) {
            }
        }
    }
}
