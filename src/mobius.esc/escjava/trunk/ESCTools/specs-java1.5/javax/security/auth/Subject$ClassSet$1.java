package javax.security.auth;

import java.util.*;
import java.io.*;
import java.lang.reflect.*;

class Subject$ClassSet$1 implements java.security.PrivilegedAction {
    /*synthetic*/ final Subject$ClassSet this$1;
    /*synthetic*/ final Iterator val$iterator;
    
    Subject$ClassSet$1(/*synthetic*/ final Subject$ClassSet this$1, /*synthetic*/ final Iterator val$iterator) {
        this.this$1 = this$1;
        this.val$iterator = val$iterator;
        
    }
    
    public Object run() {
        return val$iterator.next();
    }
}
