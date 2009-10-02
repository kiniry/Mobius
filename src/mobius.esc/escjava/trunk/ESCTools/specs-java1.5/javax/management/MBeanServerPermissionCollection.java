package javax.management;

import java.security.Permission;
import java.security.PermissionCollection;
import java.util.Collections;
import java.util.Enumeration;
import java.util.Set;

class MBeanServerPermissionCollection extends PermissionCollection {
    
    MBeanServerPermissionCollection() {
        
    }
    private MBeanServerPermission collectionPermission;
    private static final long serialVersionUID = -5661980843569388590L;
    
    public synchronized void add(Permission permission) {
        if (!(permission instanceof MBeanServerPermission)) {
            final String msg = "Permission not an MBeanServerPermission: " + permission;
            throw new IllegalArgumentException(msg);
        }
        if (isReadOnly()) throw new SecurityException("Read-only permission collection");
        MBeanServerPermission mbsp = (MBeanServerPermission)(MBeanServerPermission)permission;
        if (collectionPermission == null) collectionPermission = mbsp; else if (!collectionPermission.implies(permission)) {
            int newmask = collectionPermission.mask | mbsp.mask;
            collectionPermission = new MBeanServerPermission(newmask);
        }
    }
    
    public synchronized boolean implies(Permission permission) {
        return (collectionPermission != null && collectionPermission.implies(permission));
    }
    
    public synchronized Enumeration elements() {
        Set set;
        if (collectionPermission == null) set = Collections.EMPTY_SET; else set = Collections.singleton(collectionPermission);
        return Collections.enumeration(set);
    }
}
