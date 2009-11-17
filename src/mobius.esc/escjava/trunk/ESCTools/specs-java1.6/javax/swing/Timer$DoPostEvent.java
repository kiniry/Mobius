package javax.swing;

import java.util.*;
import java.awt.*;
import java.awt.event.*;
import java.io.Serializable;

class Timer$DoPostEvent implements Runnable, Serializable {
    /*synthetic*/ final Timer this$0;
    
    Timer$DoPostEvent(/*synthetic*/ final Timer this$0) {
        this.this$0 = this$0;
        
    }
    
    public void run() {
        if (Timer.access$000()) {
            System.out.println("Timer ringing: " + this$0);
        }
        if (Timer.access$100(this$0)) {
            this$0.fireActionPerformed(new ActionEvent(this$0, 0, null, System.currentTimeMillis(), 0));
            if (this$0.coalesce) {
                this$0.cancelEvent();
            }
        }
    }
    
    Timer getTimer() {
        return this$0;
    }
}
