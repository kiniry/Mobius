package java.security;

import java.io.*;
import java.util.Enumeration;
import java.lang.reflect.*;
import java.util.WeakHashMap;
import sun.security.util.Debug;
import sun.security.util.SecurityConstants;

public abstract class Policy {
    
    public Policy() {
        
    }
    private static Policy policy;
    private static final Debug debug = Debug.getInstance("policy");
    private WeakHashMap pdMapping;
    
    static boolean isSet() {
        return policy != null;
    }
    
    public static Policy getPolicy() {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) sm.checkPermission(SecurityConstants.GET_POLICY_PERMISSION);
        return getPolicyNoCheck();
    }
    
    static synchronized Policy getPolicyNoCheck() {
        if (policy == null) {
            String policy_class = null;
            policy_class = (String)(String)AccessController.doPrivileged(new Policy$1());
            if (policy_class == null) {
                policy_class = "sun.security.provider.PolicyFile";
            }
            policy = new sun.security.provider.PolicyFile(true);
            try {
                policy = (Policy)(Policy)Class.forName(policy_class).newInstance();
            } catch (Exception e) {
                final String pc = policy_class;
                Policy p = (Policy)(Policy)AccessController.doPrivileged(new Policy$2(pc));
                if (p != null) policy = p;
                if (p == null && debug != null) {
                    debug.println("policy provider " + policy_class + " not available;using " + "sun.security.provider.PolicyFile");
                    e.printStackTrace();
                }
            }
        }
        return policy;
    }
    
    public static void setPolicy(Policy p) {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) sm.checkPermission(new SecurityPermission("setPolicy"));
        if (p != null) {
            initPolicy(p);
        }
        synchronized (Policy.class) {
            Policy.policy = p;
        }
    }
    
    private static void initPolicy(final Policy p) {
        ProtectionDomain policyDomain = (ProtectionDomain)(ProtectionDomain)AccessController.doPrivileged(new Policy$3(p));
        PermissionCollection policyPerms = null;
        synchronized (p) {
            if (p.pdMapping == null) {
                p.pdMapping = new WeakHashMap();
            }
        }
        if (policyDomain.getCodeSource() != null) {
            if (Policy.isSet()) {
                policyPerms = policy.getPermissions(policyDomain);
            }
            if (policyPerms == null) {
                policyPerms = new Permissions();
                policyPerms.add(SecurityConstants.ALL_PERMISSION);
            }
            synchronized (p.pdMapping) {
                p.pdMapping.put(policyDomain, policyPerms);
            }
        }
        return;
    }
    
    public abstract PermissionCollection getPermissions(CodeSource codesource);
    
    public PermissionCollection getPermissions(ProtectionDomain domain) {
        PermissionCollection pc = null;
        if (domain == null) return new Permissions();
        if (pdMapping == null) {
            initPolicy(this);
        }
        synchronized (pdMapping) {
            pc = (PermissionCollection)(PermissionCollection)pdMapping.get(domain);
        }
        if (pc != null) {
            Permissions perms = new Permissions();
            synchronized (pc) {
                for (Enumeration e = pc.elements(); e.hasMoreElements(); ) {
                    perms.add((Permission)(Permission)e.nextElement());
                }
            }
            return perms;
        }
        pc = getPermissions(domain.getCodeSource());
        if (pc == null) {
            pc = new Permissions();
        }
        addStaticPerms(pc, domain.getPermissions());
        return pc;
    }
    
    private void addStaticPerms(PermissionCollection perms, PermissionCollection statics) {
        if (statics != null) {
            synchronized (statics) {
                Enumeration e = statics.elements();
                while (e.hasMoreElements()) {
                    perms.add((Permission)(Permission)e.nextElement());
                }
            }
        }
    }
    
    public boolean implies(ProtectionDomain domain, Permission permission) {
        PermissionCollection pc;
        if (pdMapping == null) {
            initPolicy(this);
        }
        synchronized (pdMapping) {
            pc = (PermissionCollection)(PermissionCollection)pdMapping.get(domain);
        }
        if (pc != null) {
            return pc.implies(permission);
        }
        pc = getPermissions(domain);
        if (pc == null) {
            return false;
        }
        synchronized (pdMapping) {
            pdMapping.put(domain, pc);
        }
        return pc.implies(permission);
    }
    
    public abstract void refresh();
}
