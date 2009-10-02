package javax.security.auth;

import java.util.*;
import java.io.*;
import java.lang.reflect.*;
import java.security.AccessControlContext;
import java.security.DomainCombiner;

class Subject$1 implements java.security.PrivilegedAction {
    /*synthetic*/ final AccessControlContext val$acc;
    
    Subject$1(/*synthetic*/ final AccessControlContext val$acc) {
        this.val$acc = val$acc;
        
    }
    
    public Object run() {
        DomainCombiner dc = val$acc.getDomainCombiner();
        if (!(dc instanceof SubjectDomainCombiner)) return null;
        SubjectDomainCombiner sdc = (SubjectDomainCombiner)(SubjectDomainCombiner)dc;
        return sdc.getSubject();
    }
}
