package java.security;

import java.security.*;
import java.util.Enumeration;
import java.util.Map;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.Collections;
import java.io.ObjectStreamField;
import java.io.ObjectOutputStream;
import java.io.IOException;

final class BasicPermissionCollection extends PermissionCollection implements java.io.Serializable {
    private static final long serialVersionUID = 739301742472979399L;
    private transient Map perms;
    private boolean all_allowed;
    private Class permClass;
    
    public BasicPermissionCollection() {
        
        perms = new HashMap(11);
        all_allowed = false;
    }
    
    public void add(Permission permission) {
        if (!(permission instanceof BasicPermission)) throw new IllegalArgumentException("invalid permission: " + permission);
        if (isReadOnly()) throw new SecurityException("attempt to add a Permission to a readonly PermissionCollection");
        BasicPermission bp = (BasicPermission)(BasicPermission)permission;
        if (perms.size() == 0) {
            permClass = bp.getClass();
        } else {
            if (bp.getClass() != permClass) throw new IllegalArgumentException("invalid permission: " + permission);
        }
        synchronized (this) {
            perms.put(bp.getName(), permission);
        }
        if (!all_allowed) {
            if (bp.getName().equals("*")) all_allowed = true;
        }
    }
    
    public boolean implies(Permission permission) {
        if (!(permission instanceof BasicPermission)) return false;
        BasicPermission bp = (BasicPermission)(BasicPermission)permission;
        if (bp.getClass() != permClass) return false;
        if (all_allowed) return true;
        String path = bp.getName();
        Permission x;
        synchronized (this) {
            x = (Permission)(Permission)perms.get(path);
        }
        if (x != null) {
            return x.implies(permission);
        }
        int last;
        int offset;
        offset = path.length() - 1;
        while ((last = path.lastIndexOf(".", offset)) != -1) {
            path = path.substring(0, last + 1) + "*";
            synchronized (this) {
                x = (Permission)(Permission)perms.get(path);
            }
            if (x != null) {
                return x.implies(permission);
            }
            offset = last - 1;
        }
        return false;
    }
    
    public Enumeration elements() {
        synchronized (this) {
            return Collections.enumeration(perms.values());
        }
    }
    private static final ObjectStreamField[] serialPersistentFields = {new ObjectStreamField("permissions", Hashtable.class), new ObjectStreamField("all_allowed", Boolean.TYPE), new ObjectStreamField("permClass", Class.class)};
    
    private void writeObject(ObjectOutputStream out) throws IOException {
        Hashtable permissions = new Hashtable(perms.size() * 2);
        synchronized (this) {
            permissions.putAll(perms);
        }
        ObjectOutputStream$PutField pfields = out.putFields();
        pfields.put("all_allowed", all_allowed);
        pfields.put("permissions", permissions);
        pfields.put("permClass", permClass);
        out.writeFields();
    }
    
    private void readObject(java.io.ObjectInputStream in) throws IOException, ClassNotFoundException {
        ObjectInputStream$GetField gfields = in.readFields();
        Hashtable permissions = (Hashtable)(Hashtable)gfields.get("permissions", null);
        perms = new HashMap(permissions.size() * 2);
        perms.putAll(permissions);
        all_allowed = gfields.get("all_allowed", false);
        permClass = (Class)(Class)gfields.get("permClass", null);
        if (permClass == null) {
            Enumeration e = permissions.elements();
            if (e.hasMoreElements()) {
                Permission p = (Permission)(Permission)e.nextElement();
                permClass = p.getClass();
            }
        }
    }
}
