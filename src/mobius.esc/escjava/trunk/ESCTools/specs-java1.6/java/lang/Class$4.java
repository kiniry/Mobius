package java.lang;

import java.lang.reflect.Method;
import sun.reflect.annotation.*;

class Class$4 implements java.security.PrivilegedAction {
    /*synthetic*/ final Class this$0;
    /*synthetic*/ final Method val$values;
    
    Class$4(/*synthetic*/ final Class this$0, /*synthetic*/ final Method val$values) {
        this.this$0 = this$0;
        this.val$values = val$values;
        
    }
    
    public Object run() {
        val$values.setAccessible(true);
        return null;
    }
}
