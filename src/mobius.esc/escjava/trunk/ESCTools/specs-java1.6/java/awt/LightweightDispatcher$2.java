package java.awt;

import javax.accessibility.*;

class LightweightDispatcher$2 implements java.security.PrivilegedAction {
    /*synthetic*/ final LightweightDispatcher this$0;
    
    LightweightDispatcher$2(/*synthetic*/ final LightweightDispatcher this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        LightweightDispatcher.access$000(this$0).getToolkit().removeAWTEventListener(this$0);
        return null;
    }
}
