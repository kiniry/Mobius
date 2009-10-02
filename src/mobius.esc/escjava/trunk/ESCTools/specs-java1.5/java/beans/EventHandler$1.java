package java.beans;

import java.lang.reflect.Method;
import java.security.PrivilegedAction;

class EventHandler$1 implements PrivilegedAction {
    /*synthetic*/ final EventHandler this$0;
    /*synthetic*/ final Object[] val$arguments;
    /*synthetic*/ final Method val$method;
    /*synthetic*/ final Object val$proxy;
    
    EventHandler$1(/*synthetic*/ final EventHandler this$0, /*synthetic*/ final Object val$proxy, /*synthetic*/ final Method val$method, /*synthetic*/ final Object[] val$arguments) {
        this.this$0 = this$0;
        this.val$proxy = val$proxy;
        this.val$method = val$method;
        this.val$arguments = val$arguments;
        
    }
    
    public Object run() {
        return EventHandler.access$000(this$0, val$proxy, val$method, val$arguments);
    }
}
