package com.sun.security.auth;

import java.util.*;
import javax.security.auth.Subject;

class SubjectCodeSource$3 implements java.security.PrivilegedAction {
    /*synthetic*/ final SubjectCodeSource this$0;
    /*synthetic*/ final Subject val$finalSubject;
    
    SubjectCodeSource$3(/*synthetic*/ final SubjectCodeSource this$0, /*synthetic*/ final Subject val$finalSubject) {
        this.this$0 = this$0;
        this.val$finalSubject = val$finalSubject;
        
    }
    
    public Object run() {
        return val$finalSubject.toString();
    }
}
