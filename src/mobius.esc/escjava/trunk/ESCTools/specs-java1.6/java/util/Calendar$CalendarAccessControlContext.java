package java.util;

import java.security.AccessControlContext;
import java.security.PermissionCollection;
import java.security.ProtectionDomain;

class Calendar$CalendarAccessControlContext {
    
    /*synthetic*/ static AccessControlContext access$000() {
        return INSTANCE;
    }
    
    private Calendar$CalendarAccessControlContext() {
        
    }
    private static final AccessControlContext INSTANCE;
    static {
        RuntimePermission perm = new RuntimePermission("accessClassInPackage.sun.util.calendar");
        PermissionCollection perms = perm.newPermissionCollection();
        perms.add(perm);
        INSTANCE = new AccessControlContext(new ProtectionDomain[]{new ProtectionDomain(null, perms)});
    }
}
