package javax.security.auth;

import java.util.*;
import java.io.*;
import java.lang.reflect.*;
import java.security.Principal;
import sun.security.util.ResourcesMgr;

class Subject$SecureSet extends AbstractSet implements java.io.Serializable {
    
    /*synthetic*/ static int access$000(Subject$SecureSet x0) {
        return x0.which;
    }
    private static final long serialVersionUID = 7911754171111800359L;
    private static final ObjectStreamField[] serialPersistentFields = {new ObjectStreamField("this$0", Subject.class), new ObjectStreamField("elements", LinkedList.class), new ObjectStreamField("which", Integer.TYPE)};
    Subject subject;
    LinkedList elements;
    private int which;
    
    Subject$SecureSet(Subject subject, int which) {
        
        this.subject = subject;
        this.which = which;
        this.elements = new LinkedList();
    }
    
    Subject$SecureSet(Subject subject, int which, Set set) {
        
        this.subject = subject;
        this.which = which;
        this.elements = new LinkedList(set);
    }
    
    public int size() {
        return elements.size();
    }
    
    public Iterator iterator() {
        final LinkedList list = elements;
        return new Subject$SecureSet$1(this, list);
    }
    
    public boolean add(Object o) {
        if (subject.isReadOnly()) {
            throw new IllegalStateException(ResourcesMgr.getString("Subject is read-only"));
        }
        java.lang.SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            switch (which) {
            case 1: 
                sm.checkPermission(new AuthPermission("modifyPrincipals"));
                break;
            
            case 2: 
                sm.checkPermission(new AuthPermission("modifyPublicCredentials"));
                break;
            
            default: 
                sm.checkPermission(new AuthPermission("modifyPrivateCredentials"));
                break;
            
            }
        }
        switch (which) {
        case 1: 
            if (!(o instanceof Principal)) {
                throw new SecurityException(ResourcesMgr.getString("attempting to add an object which is not an instance of java.security.Principal to a Subject\'s Principal Set"));
            }
            break;
        
        default: 
            break;
        
        }
        if (!elements.contains(o)) return elements.add(o); else return false;
    }
    
    public boolean remove(Object o) {
        final Iterator e = iterator();
        while (e.hasNext()) {
            Object next;
            if (which != 3) {
                next = e.next();
            } else {
                next = (Object)java.security.AccessController.doPrivileged(new Subject$SecureSet$2(this, e));
            }
            if (next == null) {
                if (o == null) {
                    e.remove();
                    return true;
                }
            } else if (next.equals(o)) {
                e.remove();
                return true;
            }
        }
        return false;
    }
    
    public boolean contains(Object o) {
        final Iterator e = iterator();
        while (e.hasNext()) {
            Object next;
            if (which != 3) {
                next = e.next();
            } else {
                SecurityManager sm = System.getSecurityManager();
                if (sm != null) {
                    sm.checkPermission(new PrivateCredentialPermission(o.getClass().getName(), subject.getPrincipals()));
                }
                next = (Object)java.security.AccessController.doPrivileged(new Subject$SecureSet$3(this, e));
            }
            if (next == null) {
                if (o == null) {
                    return true;
                }
            } else if (next.equals(o)) {
                return true;
            }
        }
        return false;
    }
    
    public boolean removeAll(Collection c) {
        boolean modified = false;
        final Iterator e = iterator();
        while (e.hasNext()) {
            Object next;
            if (which != 3) {
                next = e.next();
            } else {
                next = (Object)java.security.AccessController.doPrivileged(new Subject$SecureSet$4(this, e));
            }
            Iterator ce = c.iterator();
            while (ce.hasNext()) {
                Object o = ce.next();
                if (next == null) {
                    if (o == null) {
                        e.remove();
                        modified = true;
                        break;
                    }
                } else if (next.equals(o)) {
                    e.remove();
                    modified = true;
                    break;
                }
            }
        }
        return modified;
    }
    
    public boolean retainAll(Collection c) {
        boolean modified = false;
        boolean retain = false;
        final Iterator e = iterator();
        while (e.hasNext()) {
            retain = false;
            Object next;
            if (which != 3) {
                next = e.next();
            } else {
                next = (Object)java.security.AccessController.doPrivileged(new Subject$SecureSet$5(this, e));
            }
            Iterator ce = c.iterator();
            while (ce.hasNext()) {
                Object o = ce.next();
                if (next == null) {
                    if (o == null) {
                        retain = true;
                        break;
                    }
                } else if (next.equals(o)) {
                    retain = true;
                    break;
                }
            }
            if (!retain) {
                e.remove();
                retain = false;
                modified = true;
            }
        }
        return modified;
    }
    
    public void clear() {
        final Iterator e = iterator();
        while (e.hasNext()) {
            Object next;
            if (which != 3) {
                next = e.next();
            } else {
                next = (Object)java.security.AccessController.doPrivileged(new Subject$SecureSet$6(this, e));
            }
            e.remove();
        }
    }
    
    private synchronized void writeObject(java.io.ObjectOutputStream oos) throws java.io.IOException {
        if (which == 3) {
            Iterator i = iterator();
            while (i.hasNext()) {
                i.next();
            }
        }
        ObjectOutputStream$PutField fields = oos.putFields();
        fields.put("this$0", subject);
        fields.put("elements", elements);
        fields.put("which", which);
        oos.writeFields();
    }
    
    private void readObject(ObjectInputStream ois) throws IOException, ClassNotFoundException {
        ObjectInputStream$GetField fields = ois.readFields();
        subject = (Subject)(Subject)fields.get("this$0", null);
        elements = (LinkedList)(LinkedList)fields.get("elements", null);
        which = fields.get("which", 0);
    }
}
