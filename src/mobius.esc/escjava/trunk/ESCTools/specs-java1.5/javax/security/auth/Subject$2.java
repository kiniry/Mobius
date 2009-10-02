package javax.security.auth;

import java.util.*;
import java.io.*;
import java.lang.reflect.*;
import java.security.AccessControlContext;

class Subject$2 implements java.security.PrivilegedAction {
    /*synthetic*/ final AccessControlContext val$acc;
    /*synthetic*/ final Subject val$subject;
    
    Subject$2(/*synthetic*/ final Subject val$subject, /*synthetic*/ final AccessControlContext val$acc) {
        this.val$subject = val$subject;
        this.val$acc = val$acc;
        
    }
    
    public Object run() {
        if (val$subject == null) return new AccessControlContext(val$acc, null); else return new AccessControlContext(val$acc, new SubjectDomainCombiner(val$subject));
    }
}
