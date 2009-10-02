package java.io;

import java.security.*;
import java.util.Enumeration;
import java.util.List;
import java.util.ArrayList;
import java.util.Vector;
import java.util.Collections;
import java.io.ObjectStreamField;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import java.io.IOException;

final class FilePermissionCollection extends PermissionCollection implements Serializable {
    private transient List perms;
    
    public FilePermissionCollection() {
        
        perms = new ArrayList();
    }
    
    public void add(Permission permission) {
        if (!(permission instanceof FilePermission)) throw new IllegalArgumentException("invalid permission: " + permission);
        if (isReadOnly()) throw new SecurityException("attempt to add a Permission to a readonly PermissionCollection");
        synchronized (this) {
            perms.add(permission);
        }
    }
    
    public boolean implies(Permission permission) {
        if (!(permission instanceof FilePermission)) return false;
        FilePermission fp = (FilePermission)(FilePermission)permission;
        int desired = fp.getMask();
        int effective = 0;
        int needed = desired;
        synchronized (this) {
            int len = perms.size();
            for (int i = 0; i < len; i++) {
                FilePermission x = (FilePermission)(FilePermission)perms.get(i);
                if (((needed & x.getMask()) != 0) && x.impliesIgnoreMask(fp)) {
                    effective |= x.getMask();
                    if ((effective & desired) == desired) return true;
                    needed = (desired ^ effective);
                }
            }
        }
        return false;
    }
    
    public Enumeration elements() {
        synchronized (this) {
            return Collections.enumeration(perms);
        }
    }
    private static final long serialVersionUID = 2202956749081564585L;
    private static final ObjectStreamField[] serialPersistentFields = {new ObjectStreamField("permissions", Vector.class)};
    
    private void writeObject(ObjectOutputStream out) throws IOException {
        Vector permissions = new Vector(perms.size());
        synchronized (this) {
            permissions.addAll(perms);
        }
        ObjectOutputStream$PutField pfields = out.putFields();
        pfields.put("permissions", permissions);
        out.writeFields();
    }
    
    private void readObject(ObjectInputStream in) throws IOException, ClassNotFoundException {
        ObjectInputStream$GetField gfields = in.readFields();
        Vector permissions = (Vector)(Vector)gfields.get("permissions", null);
        perms = new ArrayList(permissions.size());
        perms.addAll(permissions);
    }
}
