package java.awt;

import java.awt.event.*;
import java.lang.reflect.Method;
import javax.accessibility.*;
import java.security.PrivilegedAction;
import javax.accessibility.*;
import java.util.logging.*;

class Component$3 implements PrivilegedAction {
    /*synthetic*/ final Component this$0;
    /*synthetic*/ final Method val$method;
    
    Component$3(/*synthetic*/ final Component this$0, /*synthetic*/ final Method val$method) {
        this.this$0 = this$0;
        this.val$method = val$method;
        
    }
    
    public Object run() {
        val$method.setAccessible(true);
        return null;
    }
}
