package java.awt;

import javax.accessibility.*;

class LightweightDispatcher$1 implements java.security.PrivilegedAction {
    /*synthetic*/ final LightweightDispatcher this$0;
    
    LightweightDispatcher$1(/*synthetic*/ final LightweightDispatcher this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        LightweightDispatcher.access$000(this$0).getToolkit().addAWTEventListener(this$0, AWTEvent.MOUSE_EVENT_MASK | AWTEvent.MOUSE_MOTION_EVENT_MASK);
        return null;
    }
}
