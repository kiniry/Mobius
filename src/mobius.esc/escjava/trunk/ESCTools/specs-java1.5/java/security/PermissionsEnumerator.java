package java.security;

import java.util.Enumeration;
import java.util.NoSuchElementException;
import java.util.Iterator;

final class PermissionsEnumerator implements Enumeration {
    private Iterator perms;
    private Enumeration permset;
    
    PermissionsEnumerator(Iterator e) {
        
        perms = e;
        permset = getNextEnumWithMore();
    }
    
    public boolean hasMoreElements() {
        if (permset == null) return false;
        if (permset.hasMoreElements()) return true;
        permset = getNextEnumWithMore();
        return (permset != null);
    }
    
    public Permission nextElement() {
        if (hasMoreElements()) {
            return (Permission)permset.nextElement();
        } else {
            throw new NoSuchElementException("PermissionsEnumerator");
        }
    }
    
    private Enumeration getNextEnumWithMore() {
        while (perms.hasNext()) {
            PermissionCollection pc = (PermissionCollection)(PermissionCollection)perms.next();
            Enumeration next = pc.elements();
            if (next.hasMoreElements()) return next;
        }
        return null;
    }
    
    /*synthetic public Object nextElement() {
        return this.nextElement();
    }*/
}
