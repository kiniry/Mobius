package java.security;

public abstract class Permission implements Guard, java.io.Serializable {
    private static final long serialVersionUID = -5636570222231596674L;
    private String name;
    
    public Permission(String name) {
        
        this.name = name;
    }
    
    public void checkGuard(Object object) throws SecurityException {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) sm.checkPermission(this);
    }
    
    public abstract boolean implies(Permission permission);
    
    public abstract boolean equals(Object obj);
    
    public abstract int hashCode();
    
    public final String getName() {
        return name;
    }
    
    public abstract String getActions();
    
    public PermissionCollection newPermissionCollection() {
        return null;
    }
    
    public String toString() {
        String actions = getActions();
        if ((actions == null) || (actions.length() == 0)) {
            return "(" + getClass().getName() + " " + name + ")";
        } else {
            return "(" + getClass().getName() + " " + name + " " + actions + ")";
        }
    }
}
