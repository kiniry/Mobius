package java.security;

import sun.security.util.Debug;

public final class AccessController {
    
    private AccessController() {
        
    }
    
    public static native Object doPrivileged(PrivilegedAction action);
    
    public static native Object doPrivileged(PrivilegedAction action, AccessControlContext context);
    
    public static native Object doPrivileged(PrivilegedExceptionAction action) throws PrivilegedActionException;
    
    public static native Object doPrivileged(PrivilegedExceptionAction action, AccessControlContext context) throws PrivilegedActionException;
    
    private static native AccessControlContext getStackAccessControlContext();
    
    static native AccessControlContext getInheritedAccessControlContext();
    
    public static AccessControlContext getContext() {
        AccessControlContext acc = getStackAccessControlContext();
        if (acc == null) {
            return new AccessControlContext(null, true);
        } else {
            return acc.optimize();
        }
    }
    
    public static void checkPermission(Permission perm) throws AccessControlException {
        AccessControlContext stack = getStackAccessControlContext();
        if (stack == null) {
            Debug debug = AccessControlContext.getDebug();
            if (debug != null) {
                if (Debug.isOn("stack")) Thread.currentThread().dumpStack();
                if (Debug.isOn("domain")) {
                    debug.println("domain (context is null)");
                }
                debug.println("access allowed " + perm);
            }
            return;
        }
        AccessControlContext acc = stack.optimize();
        acc.checkPermission(perm);
    }
}
