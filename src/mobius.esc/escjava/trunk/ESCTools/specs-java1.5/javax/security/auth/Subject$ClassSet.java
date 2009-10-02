package javax.security.auth;

import java.util.*;
import java.io.*;
import java.lang.reflect.*;
import java.text.MessageFormat;
import sun.security.util.ResourcesMgr;

class Subject$ClassSet extends AbstractSet {
    /*synthetic*/ final Subject this$0;
    private int which;
    private Class c;
    private Set set;
    
    Subject$ClassSet(/*synthetic*/ final Subject this$0, int which, Class c) {
        this.this$0 = this$0;
        
        this.which = which;
        this.c = c;
        set = new HashSet();
        switch (which) {
        case 1: 
            synchronized (this$0.principals) {
                populateSet();
            }
            break;
        
        case 2: 
            synchronized (this$0.pubCredentials) {
                populateSet();
            }
            break;
        
        default: 
            synchronized (this$0.privCredentials) {
                populateSet();
            }
            break;
        
        }
    }
    
    private void populateSet() {
        final Iterator iterator;
        switch (which) {
        case 1: 
            iterator = this$0.principals.iterator();
            break;
        
        case 2: 
            iterator = this$0.pubCredentials.iterator();
            break;
        
        default: 
            iterator = this$0.privCredentials.iterator();
            break;
        
        }
        while (iterator.hasNext()) {
            Object next;
            if (which == 3) {
                next = (Object)java.security.AccessController.doPrivileged(new Subject$ClassSet$1(this, iterator));
            } else {
                next = iterator.next();
            }
            if (c.isAssignableFrom(next.getClass())) {
                if (which != 3) {
                    set.add((Object)next);
                } else {
                    SecurityManager sm = System.getSecurityManager();
                    if (sm != null) {
                        sm.checkPermission(new PrivateCredentialPermission(next.getClass().getName(), this$0.getPrincipals()));
                    }
                    set.add((Object)next);
                }
            }
        }
    }
    
    public int size() {
        return set.size();
    }
    
    public Iterator iterator() {
        return set.iterator();
    }
    
    public boolean add(Object o) {
        if (!o.getClass().isAssignableFrom(c)) {
            MessageFormat form = new MessageFormat(ResourcesMgr.getString("attempting to add an object which is not an instance of class"));
            Object[] source = {c.toString()};
            throw new SecurityException(form.format(source));
        }
        return set.add(o);
    }
}
