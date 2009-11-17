package java.lang;

import java.lang.reflect.Constructor;
import sun.reflect.annotation.*;

class Class$1 implements java.security.PrivilegedAction {
    /*synthetic*/ final Class this$0;
    /*synthetic*/ final Constructor val$c;
    
    Class$1(/*synthetic*/ final Class this$0, /*synthetic*/ final Constructor val$c) {
        this.this$0 = this$0;
        this.val$c = val$c;
        
    }
    
    public Object run() {
        val$c.setAccessible(true);
        return null;
    }
}
