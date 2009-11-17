package java.security;

import java.security.*;
import java.io.ObjectInputStream;
import java.io.IOException;

public abstract class BasicPermission extends Permission implements java.io.Serializable {
    private static final long serialVersionUID = 6279438298436773498L;
    private transient boolean wildcard;
    private transient String path;
    
    private void init(String name) {
        if (name == null) throw new NullPointerException("name can\'t be null");
        int len = name.length();
        if (len == 0) {
            throw new IllegalArgumentException("name can\'t be empty");
        }
        char last = name.charAt(len - 1);
        if (last == '*' && (len == 1 || name.charAt(len - 2) == '.')) {
            wildcard = true;
            if (len == 1) {
                path = "";
            } else {
                path = name.substring(0, len - 1);
            }
        } else {
            path = name;
        }
    }
    
    public BasicPermission(String name) {
        super(name);
        init(name);
    }
    
    public BasicPermission(String name, String actions) {
        super(name);
        init(name);
    }
    
    public boolean implies(Permission p) {
        if ((p == null) || (p.getClass() != getClass())) return false;
        BasicPermission that = (BasicPermission)(BasicPermission)p;
        if (this.wildcard) {
            if (that.wildcard) return that.path.startsWith(path); else return (that.path.length() > this.path.length()) && that.path.startsWith(this.path);
        } else {
            if (that.wildcard) {
                return false;
            } else {
                return this.path.equals(that.path);
            }
        }
    }
    
    public boolean equals(Object obj) {
        if (obj == this) return true;
        if ((obj == null) || (obj.getClass() != getClass())) return false;
        BasicPermission bp = (BasicPermission)(BasicPermission)obj;
        return getName().equals(bp.getName());
    }
    
    public int hashCode() {
        return this.getName().hashCode();
    }
    
    public String getActions() {
        return "";
    }
    
    public PermissionCollection newPermissionCollection() {
        return new BasicPermissionCollection();
    }
    
    private void readObject(ObjectInputStream s) throws IOException, ClassNotFoundException {
        s.defaultReadObject();
        init(getName());
    }
}
