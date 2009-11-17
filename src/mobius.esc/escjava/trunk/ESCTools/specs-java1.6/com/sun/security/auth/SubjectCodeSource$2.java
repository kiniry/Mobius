package com.sun.security.auth;

import java.util.*;

class SubjectCodeSource$2 implements java.security.PrivilegedAction {
    /*synthetic*/ final SubjectCodeSource this$0;
    
    SubjectCodeSource$2(/*synthetic*/ final SubjectCodeSource this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        return ClassLoader.getSystemClassLoader();
    }
}
