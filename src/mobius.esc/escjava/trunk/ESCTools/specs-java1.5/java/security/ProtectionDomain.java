package java.security;

import java.util.Enumeration;
import java.util.List;
import java.util.ArrayList;
import sun.security.util.Debug;
import sun.security.util.SecurityConstants;

public class ProtectionDomain {
    private CodeSource codesource;
    private ClassLoader classloader;
    private Principal[] principals;
    private PermissionCollection permissions;
    private boolean staticPermissions;
    private static final Debug debug = Debug.getInstance("domain");
    
    public ProtectionDomain(CodeSource codesource, PermissionCollection permissions) {
        
        this.codesource = codesource;
        if (permissions != null) {
            this.permissions = permissions;
            this.permissions.setReadOnly();
        }
        this.classloader = null;
        this.principals = new Principal[0];
        staticPermissions = true;
    }
    
    public ProtectionDomain(CodeSource codesource, PermissionCollection permissions, ClassLoader classloader, Principal[] principals) {
        
        this.codesource = codesource;
        if (permissions != null) {
            this.permissions = permissions;
            this.permissions.setReadOnly();
        }
        this.classloader = classloader;
        this.principals = (principals != null ? (Principal[])(Principal[])principals.clone() : new Principal[0]);
        staticPermissions = false;
    }
    
    public final CodeSource getCodeSource() {
        return this.codesource;
    }
    
    public final ClassLoader getClassLoader() {
        return this.classloader;
    }
    
    public final Principal[] getPrincipals() {
        return (Principal[])(Principal[])this.principals.clone();
    }
    
    public final PermissionCollection getPermissions() {
        return permissions;
    }
    
    public boolean implies(Permission permission) {
        if (!staticPermissions && Policy.getPolicyNoCheck().implies(this, permission)) return true;
        if (permissions != null) return permissions.implies(permission);
        return false;
    }
    
    public String toString() {
        String pals = "<no principals>";
        if (principals != null && principals.length > 0) {
            StringBuilder palBuf = new StringBuilder("(principals ");
            for (int i = 0; i < principals.length; i++) {
                palBuf.append(principals[i].getClass().getName() + " \"" + principals[i].getName() + "\"");
                if (i < principals.length - 1) palBuf.append(",\n"); else palBuf.append(")\n");
            }
            pals = palBuf.toString();
        }
        PermissionCollection pc = Policy.isSet() && seeAllp() ? mergePermissions() : getPermissions();
        return "ProtectionDomain " + " " + codesource + "\n" + " " + classloader + "\n" + " " + pals + "\n" + " " + pc + "\n";
    }
    
    private static boolean seeAllp() {
        SecurityManager sm = System.getSecurityManager();
        if (sm == null) {
            return true;
        } else {
            if (debug != null) {
                if (sm.getClass().getClassLoader() == null && Policy.getPolicyNoCheck().getClass().getClassLoader() == null) {
                    return true;
                }
            } else {
                try {
                    sm.checkPermission(SecurityConstants.GET_POLICY_PERMISSION);
                    return true;
                } catch (SecurityException se) {
                }
            }
        }
        return false;
    }
    
    private PermissionCollection mergePermissions() {
        if (staticPermissions) return permissions;
        PermissionCollection perms = (PermissionCollection)(PermissionCollection)java.security.AccessController.doPrivileged(new ProtectionDomain$1(this));
        Permissions mergedPerms = new Permissions();
        int swag = 32;
        int vcap = 8;
        Enumeration e;
        List pdVector = new ArrayList(vcap);
        List plVector = new ArrayList(swag);
        if (permissions != null) {
            synchronized (permissions) {
                e = permissions.elements();
                while (e.hasMoreElements()) {
                    Permission p = (Permission)(Permission)e.nextElement();
                    pdVector.add(p);
                }
            }
        }
        if (perms != null) {
            synchronized (perms) {
                e = perms.elements();
                while (e.hasMoreElements()) {
                    plVector.add(e.nextElement());
                    vcap++;
                }
            }
        }
        if (perms != null && permissions != null) {
            synchronized (permissions) {
                e = permissions.elements();
                while (e.hasMoreElements()) {
                    Permission pdp = (Permission)(Permission)e.nextElement();
                    Class pdpClass = pdp.getClass();
                    String pdpActions = pdp.getActions();
                    String pdpName = pdp.getName();
                    for (int i = 0; i < plVector.size(); i++) {
                        Permission pp = (Permission)(Permission)plVector.get(i);
                        if (pdpClass.isInstance(pp)) {
                            if (pdpName.equals(pp.getName()) && pdpActions.equals(pp.getActions())) {
                                plVector.remove(i);
                                break;
                            }
                        }
                    }
                }
            }
        }
        if (perms != null) {
            for (int i = plVector.size() - 1; i >= 0; i--) {
                mergedPerms.add((Permission)(Permission)plVector.get(i));
            }
        }
        if (permissions != null) {
            for (int i = pdVector.size() - 1; i >= 0; i--) {
                mergedPerms.add((Permission)(Permission)pdVector.get(i));
            }
        }
        return mergedPerms;
    }
}
