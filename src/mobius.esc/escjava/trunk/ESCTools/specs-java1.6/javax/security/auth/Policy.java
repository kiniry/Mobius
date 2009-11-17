package javax.security.auth;


public abstract class Policy {
    
    /*synthetic*/ static ClassLoader access$000() {
        return contextClassLoader;
    }
    private static Policy policy;
    private static ClassLoader contextClassLoader;
    static {
        contextClassLoader = (ClassLoader)(ClassLoader)java.security.AccessController.doPrivileged(new Policy$1());
    }
    {
    }
    
    protected Policy() {
        
    }
    
    public static Policy getPolicy() {
        java.lang.SecurityManager sm = System.getSecurityManager();
        if (sm != null) sm.checkPermission(new AuthPermission("getPolicy"));
        return getPolicyNoCheck();
    }
    
    static Policy getPolicyNoCheck() {
        if (policy == null) {
            synchronized (Policy.class) {
                if (policy == null) {
                    String policy_class = null;
                    policy_class = (String)(String)java.security.AccessController.doPrivileged(new Policy$2());
                    if (policy_class == null) {
                        policy_class = "com.sun.security.auth.PolicyFile";
                    }
                    try {
                        final String finalClass = policy_class;
                        policy = (Policy)(Policy)java.security.AccessController.doPrivileged(new Policy$3(finalClass));
                    } catch (Exception e) {
                        throw new SecurityException(sun.security.util.ResourcesMgr.getString("unable to instantiate Subject-based policy"));
                    }
                }
            }
        }
        return policy;
    }
    
    public static void setPolicy(Policy policy) {
        java.lang.SecurityManager sm = System.getSecurityManager();
        if (sm != null) sm.checkPermission(new AuthPermission("setPolicy"));
        Policy.policy = policy;
    }
    
    public abstract java.security.PermissionCollection getPermissions(Subject subject, java.security.CodeSource cs);
    
    public abstract void refresh();
}
