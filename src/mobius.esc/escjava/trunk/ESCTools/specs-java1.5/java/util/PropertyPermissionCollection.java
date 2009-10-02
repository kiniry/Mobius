package java.util;

import java.io.Serializable;
import java.io.IOException;
import java.security.*;
import java.util.Map;
import java.util.HashMap;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Collections;
import java.io.ObjectStreamField;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import java.io.IOException;

final class PropertyPermissionCollection extends PermissionCollection implements Serializable {
    private transient Map perms;
    private boolean all_allowed;
    
    public PropertyPermissionCollection() {
        
        perms = new HashMap(32);
        all_allowed = false;
    }
    
    public void add(Permission permission) {
        if (!(permission instanceof PropertyPermission)) throw new IllegalArgumentException("invalid permission: " + permission);
        if (isReadOnly()) throw new SecurityException("attempt to add a Permission to a readonly PermissionCollection");
        PropertyPermission pp = (PropertyPermission)(PropertyPermission)permission;
        String propName = pp.getName();
        synchronized (this) {
            PropertyPermission existing = (PropertyPermission)(PropertyPermission)perms.get(propName);
            if (existing != null) {
                int oldMask = existing.getMask();
                int newMask = pp.getMask();
                if (oldMask != newMask) {
                    int effective = oldMask | newMask;
                    String actions = PropertyPermission.getActions(effective);
                    perms.put(propName, new PropertyPermission(propName, actions));
                }
            } else {
                perms.put(propName, permission);
            }
        }
        if (!all_allowed) {
            if (propName.equals("*")) all_allowed = true;
        }
    }
    
    public boolean implies(Permission permission) {
        if (!(permission instanceof PropertyPermission)) return false;
        PropertyPermission pp = (PropertyPermission)(PropertyPermission)permission;
        PropertyPermission x;
        int desired = pp.getMask();
        int effective = 0;
        if (all_allowed) {
            synchronized (this) {
                x = (PropertyPermission)(PropertyPermission)perms.get("*");
            }
            if (x != null) {
                effective |= x.getMask();
                if ((effective & desired) == desired) return true;
            }
        }
        String name = pp.getName();
        synchronized (this) {
            x = (PropertyPermission)(PropertyPermission)perms.get(name);
        }
        if (x != null) {
            effective |= x.getMask();
            if ((effective & desired) == desired) return true;
        }
        int last;
        int offset;
        offset = name.length() - 1;
        while ((last = name.lastIndexOf(".", offset)) != -1) {
            name = name.substring(0, last + 1) + "*";
            synchronized (this) {
                x = (PropertyPermission)(PropertyPermission)perms.get(name);
            }
            if (x != null) {
                effective |= x.getMask();
                if ((effective & desired) == desired) return true;
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
    private static final long serialVersionUID = 7015263904581634791L;
    private static final ObjectStreamField[] serialPersistentFields = {new ObjectStreamField("permissions", Hashtable.class), new ObjectStreamField("all_allowed", Boolean.TYPE)};
    
    private void writeObject(ObjectOutputStream out) throws IOException {
        Hashtable permissions = new Hashtable(perms.size() * 2);
        synchronized (this) {
            permissions.putAll(perms);
        }
        ObjectOutputStream$PutField pfields = out.putFields();
        pfields.put("all_allowed", all_allowed);
        pfields.put("permissions", permissions);
        out.writeFields();
    }
    
    private void readObject(ObjectInputStream in) throws IOException, ClassNotFoundException {
        ObjectInputStream$GetField gfields = in.readFields();
        all_allowed = gfields.get("all_allowed", false);
        Hashtable permissions = (Hashtable)(Hashtable)gfields.get("permissions", null);
        perms = new HashMap(permissions.size() * 2);
        perms.putAll(permissions);
    }
}
