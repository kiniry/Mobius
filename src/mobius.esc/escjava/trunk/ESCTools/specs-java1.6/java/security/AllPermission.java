package java.security;

import java.security.*;

public final class AllPermission extends Permission {
    private static final long serialVersionUID = -2916474571451318075L;
    
    public AllPermission() {
        super("<all permissions>");
    }
    
    public AllPermission(String name, String actions) {
        this();
    }
    
    public boolean implies(Permission p) {
        return true;
    }
    
    public boolean equals(Object obj) {
        return (obj instanceof AllPermission);
    }
    
    public int hashCode() {
        return 1;
    }
    
    public String getActions() {
        return "<all actions>";
    }
    
    public PermissionCollection newPermissionCollection() {
        return new AllPermissionCollection();
    }
}
