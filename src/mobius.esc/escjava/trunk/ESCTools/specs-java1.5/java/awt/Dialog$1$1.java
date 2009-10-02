package java.awt;

import java.awt.event.*;
import javax.accessibility.*;

class Dialog$1$1 implements Conditional {
    /*synthetic*/ final Dialog$1 this$1;
    
    Dialog$1$1(/*synthetic*/ final Dialog$1 this$1) {
        this.this$1 = this$1;
        
    }
    
    public boolean evaluate() {
        return Dialog.access$000(this$1.this$0) && this$1.this$0.windowClosingException == null;
    }
}
