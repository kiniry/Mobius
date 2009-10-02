package javax.security.auth;

import java.util.*;
import java.io.*;
import java.lang.reflect.*;
import sun.security.util.ResourcesMgr;

class Subject$SecureSet$1 implements Iterator {
    /*synthetic*/ final Subject$SecureSet this$0;
    /*synthetic*/ final LinkedList val$list;
    
    Subject$SecureSet$1(/*synthetic*/ final Subject$SecureSet this$0, /*synthetic*/ final LinkedList val$list) {
        this.this$0 = this$0;
        this.val$list = val$list;
        
    }
    ListIterator i = val$list.listIterator(0);
    
    public boolean hasNext() {
        return i.hasNext();
    }
    
    public Object next() {
        if (Subject.SecureSet.access$000(this$0) != 3) {
            return i.next();
        }
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            try {
                sm.checkPermission(new PrivateCredentialPermission(val$list.get(i.nextIndex()).getClass().getName(), this$0.subject.getPrincipals()));
            } catch (SecurityException se) {
                i.next();
                throw (se);
            }
        }
        return i.next();
    }
    
    public void remove() {
        if (this$0.subject.isReadOnly()) {
            throw new IllegalStateException(ResourcesMgr.getString("Subject is read-only"));
        }
        java.lang.SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            switch (Subject.SecureSet.access$000(this$0)) {
            case 1: 
                sm.checkPermission(new AuthPermission("modifyPrincipals"));
                break;
            
            case 2: 
                sm.checkPermission(new AuthPermission("modifyPublicCredentials"));
                break;
            
            default: 
                sm.checkPermission(new AuthPermission("modifyPrivateCredentials"));
                break;
            
            }
        }
        i.remove();
    }
}
