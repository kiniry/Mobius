package java.security;

import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Map;
import java.util.HashMap;
import java.util.List;
import java.io.Serializable;
import java.io.ObjectStreamField;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import java.io.IOException;

public final class Permissions extends PermissionCollection implements Serializable {
    private transient Map permsMap;
    private transient boolean hasUnresolved = false;
    private PermissionCollection allPermission;
    
    public Permissions() {
        
        permsMap = new HashMap(11);
        allPermission = null;
    }
    
    public void add(Permission permission) {
        if (isReadOnly()) throw new SecurityException("attempt to add a Permission to a readonly Permissions object");
        PermissionCollection pc;
        synchronized (this) {
            pc = getPermissionCollection(permission, true);
            pc.add(permission);
        }
        if (permission instanceof AllPermission) {
            allPermission = pc;
        }
        if (permission instanceof UnresolvedPermission) {
            hasUnresolved = true;
        }
    }
    
    public boolean implies(Permission permission) {
        if (allPermission != null) {
            return true;
        } else {
            synchronized (this) {
                PermissionCollection pc = getPermissionCollection(permission, false);
                if (pc != null) {
                    return pc.implies(permission);
                } else {
                    return false;
                }
            }
        }
    }
    
    public Enumeration elements() {
        synchronized (this) {
            return new PermissionsEnumerator(permsMap.values().iterator());
        }
    }
    
    private PermissionCollection getPermissionCollection(Permission p, boolean createEmpty) {
        Class c = p.getClass();
        PermissionCollection pc = (PermissionCollection)(PermissionCollection)permsMap.get(c);
        if (!hasUnresolved && !createEmpty) {
            return pc;
        } else if (pc == null) {
            pc = (hasUnresolved ? getUnresolvedPermissions(p) : null);
            if (pc == null && createEmpty) {
                pc = p.newPermissionCollection();
                if (pc == null) pc = new PermissionsHash();
            }
            if (pc != null) {
                permsMap.put(c, pc);
            }
        }
        return pc;
    }
    
    private PermissionCollection getUnresolvedPermissions(Permission p) {
        UnresolvedPermissionCollection uc = (UnresolvedPermissionCollection)(UnresolvedPermissionCollection)permsMap.get(UnresolvedPermission.class);
        if (uc == null) return null;
        List unresolvedPerms = uc.getUnresolvedPermissions(p);
        if (unresolvedPerms == null) return null;
        java.security.cert.Certificate[] certs = null;
        Object[] signers = p.getClass().getSigners();
        int n = 0;
        if (signers != null) {
            for (int j = 0; j < signers.length; j++) {
                if (signers[j] instanceof java.security.cert.Certificate) {
                    n++;
                }
            }
            certs = new java.security.cert.Certificate[n];
            n = 0;
            for (int j = 0; j < signers.length; j++) {
                if (signers[j] instanceof java.security.cert.Certificate) {
                    certs[n++] = (java.security.cert.Certificate)(java.security.cert.Certificate)signers[j];
                }
            }
        }
        PermissionCollection pc = null;
        synchronized (unresolvedPerms) {
            int len = unresolvedPerms.size();
            for (int i = 0; i < len; i++) {
                UnresolvedPermission up = (UnresolvedPermission)(UnresolvedPermission)unresolvedPerms.get(i);
                Permission perm = up.resolve(p, certs);
                if (perm != null) {
                    if (pc == null) {
                        pc = p.newPermissionCollection();
                        if (pc == null) pc = new PermissionsHash();
                    }
                    pc.add(perm);
                }
            }
        }
        return pc;
    }
    private static final long serialVersionUID = 4858622370623524688L;
    private static final ObjectStreamField[] serialPersistentFields = {new ObjectStreamField("perms", Hashtable.class), new ObjectStreamField("allPermission", PermissionCollection.class)};
    
    private void writeObject(ObjectOutputStream out) throws IOException {
        Hashtable perms = new Hashtable(permsMap.size() * 2);
        synchronized (this) {
            perms.putAll(permsMap);
        }
        ObjectOutputStream$PutField pfields = out.putFields();
        pfields.put("allPermission", allPermission);
        pfields.put("perms", perms);
        out.writeFields();
    }
    
    private void readObject(ObjectInputStream in) throws IOException, ClassNotFoundException {
        ObjectInputStream$GetField gfields = in.readFields();
        allPermission = (PermissionCollection)(PermissionCollection)gfields.get("allPermission", null);
        Hashtable perms = (Hashtable)(Hashtable)gfields.get("perms", null);
        permsMap = new HashMap(perms.size() * 2);
        permsMap.putAll(perms);
        UnresolvedPermissionCollection uc = (UnresolvedPermissionCollection)(UnresolvedPermissionCollection)permsMap.get(UnresolvedPermission.class);
        hasUnresolved = (uc != null && uc.elements().hasMoreElements());
    }
}
