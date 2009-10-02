package java.security;

import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Map;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Collections;
import java.io.Serializable;
import java.io.ObjectStreamField;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import java.io.IOException;

final class PermissionsHash extends PermissionCollection implements Serializable {
    private transient Map permsMap;
    
    PermissionsHash() {
        
        permsMap = new HashMap(11);
    }
    
    public void add(Permission permission) {
        synchronized (this) {
            permsMap.put(permission, permission);
        }
    }
    
    public boolean implies(Permission permission) {
        synchronized (this) {
            Permission p = (Permission)(Permission)permsMap.get(permission);
            if (p == null) {
                Iterator enum_ = permsMap.values().iterator();
                while (enum_.hasNext()) {
                    p = (Permission)(Permission)enum_.next();
                    if (p.implies(permission)) return true;
                }
                return false;
            } else {
                return true;
            }
        }
    }
    
    public Enumeration elements() {
        synchronized (this) {
            return Collections.enumeration(permsMap.values());
        }
    }
    private static final long serialVersionUID = -8491988220802933440L;
    private static final ObjectStreamField[] serialPersistentFields = {new ObjectStreamField("perms", Hashtable.class)};
    
    private void writeObject(ObjectOutputStream out) throws IOException {
        Hashtable perms = new Hashtable(permsMap.size() * 2);
        synchronized (this) {
            perms.putAll(permsMap);
        }
        ObjectOutputStream$PutField pfields = out.putFields();
        pfields.put("perms", perms);
        out.writeFields();
    }
    
    private void readObject(ObjectInputStream in) throws IOException, ClassNotFoundException {
        ObjectInputStream$GetField gfields = in.readFields();
        Hashtable perms = (Hashtable)(Hashtable)gfields.get("perms", null);
        permsMap = new HashMap(perms.size() * 2);
        permsMap.putAll(perms);
    }
}
