package java.util;

import java.io.IOException;
import java.security.*;
import java.io.IOException;
import sun.security.util.SecurityConstants;

public final class PropertyPermission extends BasicPermission {
    private static final int READ = 1;
    private static final int WRITE = 2;
    private static final int ALL = READ | WRITE;
    private static final int NONE = 0;
    private transient int mask;
    private String actions;
    
    private void init(int mask) {
        if ((mask & ALL) != mask) throw new IllegalArgumentException("invalid actions mask");
        if (mask == NONE) throw new IllegalArgumentException("invalid actions mask");
        if (getName() == null) throw new NullPointerException("name can\'t be null");
        this.mask = mask;
    }
    
    public PropertyPermission(String name, String actions) {
        super(name, actions);
        init(getMask(actions));
    }
    
    public boolean implies(Permission p) {
        if (!(p instanceof PropertyPermission)) return false;
        PropertyPermission that = (PropertyPermission)(PropertyPermission)p;
        return ((this.mask & that.mask) == that.mask) && super.implies(that);
    }
    
    public boolean equals(Object obj) {
        if (obj == this) return true;
        if (!(obj instanceof PropertyPermission)) return false;
        PropertyPermission that = (PropertyPermission)(PropertyPermission)obj;
        return (this.mask == that.mask) && (this.getName().equals(that.getName()));
    }
    
    public int hashCode() {
        return this.getName().hashCode();
    }
    
    private static int getMask(String actions) {
        int mask = NONE;
        if (actions == null) {
            return mask;
        }
        if (actions == SecurityConstants.PROPERTY_READ_ACTION) {
            return READ;
        }
        if (actions == SecurityConstants.PROPERTY_WRITE_ACTION) {
            return WRITE;
        } else if (actions == SecurityConstants.PROPERTY_RW_ACTION) {
            return READ | WRITE;
        }
        char[] a = actions.toCharArray();
        int i = a.length - 1;
        if (i < 0) return mask;
        while (i != -1) {
            char c;
            while ((i != -1) && ((c = a[i]) == ' ' || c == '\r' || c == '\n' || c == '\f' || c == '\t')) i--;
            int matchlen;
            if (i >= 3 && (a[i - 3] == 'r' || a[i - 3] == 'R') && (a[i - 2] == 'e' || a[i - 2] == 'E') && (a[i - 1] == 'a' || a[i - 1] == 'A') && (a[i] == 'd' || a[i] == 'D')) {
                matchlen = 4;
                mask |= READ;
            } else if (i >= 4 && (a[i - 4] == 'w' || a[i - 4] == 'W') && (a[i - 3] == 'r' || a[i - 3] == 'R') && (a[i - 2] == 'i' || a[i - 2] == 'I') && (a[i - 1] == 't' || a[i - 1] == 'T') && (a[i] == 'e' || a[i] == 'E')) {
                matchlen = 5;
                mask |= WRITE;
            } else {
                throw new IllegalArgumentException("invalid permission: " + actions);
            }
            boolean seencomma = false;
            while (i >= matchlen && !seencomma) {
                switch (a[i - matchlen]) {
                case ',': 
                    seencomma = true;
                
                case ' ': 
                
                case '\r': 
                
                case '\n': 
                
                case '\f': 
                
                case '\t': 
                    break;
                
                default: 
                    throw new IllegalArgumentException("invalid permission: " + actions);
                
                }
                i--;
            }
            i -= matchlen;
        }
        return mask;
    }
    
    static String getActions(int mask) {
        StringBuilder sb = new StringBuilder();
        boolean comma = false;
        if ((mask & READ) == READ) {
            comma = true;
            sb.append("read");
        }
        if ((mask & WRITE) == WRITE) {
            if (comma) sb.append(','); else comma = true;
            sb.append("write");
        }
        return sb.toString();
    }
    
    public String getActions() {
        if (actions == null) actions = getActions(this.mask);
        return actions;
    }
    
    int getMask() {
        return mask;
    }
    
    public PermissionCollection newPermissionCollection() {
        return new PropertyPermissionCollection();
    }
    private static final long serialVersionUID = 885438825399942851L;
    
    private synchronized void writeObject(java.io.ObjectOutputStream s) throws IOException {
        if (actions == null) getActions();
        s.defaultWriteObject();
    }
    
    private synchronized void readObject(java.io.ObjectInputStream s) throws IOException, ClassNotFoundException {
        s.defaultReadObject();
        init(getMask(actions));
    }
}
