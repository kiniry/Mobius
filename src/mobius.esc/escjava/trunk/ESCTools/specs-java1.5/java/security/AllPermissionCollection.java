package java.security;

import java.security.*;
import java.util.Enumeration;

final class AllPermissionCollection extends PermissionCollection implements java.io.Serializable {
    
    /*synthetic*/ static boolean access$000(AllPermissionCollection x0) {
        return x0.all_allowed;
    }
    private static final long serialVersionUID = -4023755556366636806L;
    private boolean all_allowed;
    
    public AllPermissionCollection() {
        
        all_allowed = false;
    }
    
    public void add(Permission permission) {
        if (!(permission instanceof AllPermission)) throw new IllegalArgumentException("invalid permission: " + permission);
        if (isReadOnly()) throw new SecurityException("attempt to add a Permission to a readonly PermissionCollection");
        all_allowed = true;
    }
    
    public boolean implies(Permission permission) {
        return all_allowed;
    }
    
    public Enumeration elements() {
        return new AllPermissionCollection$1(this);
    }
}
