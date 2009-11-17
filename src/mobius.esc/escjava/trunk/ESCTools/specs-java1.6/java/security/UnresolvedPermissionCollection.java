package java.security;

import java.util.*;
import java.io.ObjectStreamField;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import java.io.IOException;

final class UnresolvedPermissionCollection extends PermissionCollection implements java.io.Serializable {
    private transient Map perms;
    
    public UnresolvedPermissionCollection() {
        
        perms = new HashMap(11);
    }
    
    public void add(Permission permission) {
        if (!(permission instanceof UnresolvedPermission)) throw new IllegalArgumentException("invalid permission: " + permission);
        UnresolvedPermission up = (UnresolvedPermission)(UnresolvedPermission)permission;
        List v;
        synchronized (this) {
            v = (List)(List)perms.get(up.getName());
            if (v == null) {
                v = new ArrayList();
                perms.put(up.getName(), v);
            }
        }
        synchronized (v) {
            v.add(up);
        }
    }
    
    List getUnresolvedPermissions(Permission p) {
        synchronized (this) {
            return (List)(List)perms.get(p.getClass().getName());
        }
    }
    
    public boolean implies(Permission permission) {
        return false;
    }
    
    public Enumeration elements() {
        List results = new ArrayList();
        synchronized (this) {
            for (Iterator iter = perms.values().iterator(); iter.hasNext(); ) {
                List l = (List)(List)iter.next();
                synchronized (l) {
                    results.addAll(l);
                }
            }
        }
        return Collections.enumeration(results);
    }
    private static final long serialVersionUID = -7176153071733132400L;
    private static final ObjectStreamField[] serialPersistentFields = {new ObjectStreamField("permissions", Hashtable.class)};
    
    private void writeObject(ObjectOutputStream out) throws IOException {
        Hashtable permissions = new Hashtable(perms.size() * 2);
        synchronized (this) {
            Set set = perms.entrySet();
            for (Iterator iter = set.iterator(); iter.hasNext(); ) {
                Map$Entry e = (Map$Entry)(Map$Entry)iter.next();
                List list = (List)(List)e.getValue();
                Vector vec = new Vector(list.size());
                synchronized (list) {
                    vec.addAll(list);
                }
                permissions.put(e.getKey(), vec);
            }
        }
        ObjectOutputStream$PutField pfields = out.putFields();
        pfields.put("permissions", permissions);
        out.writeFields();
    }
    
    private void readObject(ObjectInputStream in) throws IOException, ClassNotFoundException {
        ObjectInputStream$GetField gfields = in.readFields();
        Hashtable permissions = (Hashtable)(Hashtable)gfields.get("permissions", null);
        perms = new HashMap(permissions.size() * 2);
        Set set = permissions.entrySet();
        for (Iterator iter = set.iterator(); iter.hasNext(); ) {
            Map$Entry e = (Map$Entry)(Map$Entry)iter.next();
            Vector vec = (Vector)(Vector)e.getValue();
            List list = new ArrayList(vec.size());
            list.addAll(vec);
            perms.put(e.getKey(), list);
        }
    }
}
