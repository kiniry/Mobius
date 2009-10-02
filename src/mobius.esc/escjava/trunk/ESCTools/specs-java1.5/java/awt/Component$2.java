package java.awt;

import java.awt.event.*;
import javax.accessibility.*;
import java.security.PrivilegedAction;
import javax.accessibility.*;
import java.util.logging.*;

class Component$2 implements PrivilegedAction {
    /*synthetic*/ final Component this$0;
    /*synthetic*/ final Class val$swingClass;
    
    Component$2(/*synthetic*/ final Component this$0, /*synthetic*/ final Class val$swingClass) {
        this.this$0 = this$0;
        this.val$swingClass = val$swingClass;
        
    }
    
    public Object run() {
        return val$swingClass.getDeclaredMethods();
    }
}
