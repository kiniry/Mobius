package java.awt;

import javax.accessibility.*;

class Container$2$1 implements Conditional {
    /*synthetic*/ final Container$2 this$1;
    
    Container$2$1(/*synthetic*/ final Container$2 this$1) {
        this.this$1 = this$1;
        
    }
    
    public boolean evaluate() {
        return ((this$1.this$0.windowClosingException == null) && (this$1.val$nativeContainer.modalComp != null));
    }
}
