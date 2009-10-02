package java.io;

import java.lang.ref.ReferenceQueue;
import java.lang.ref.WeakReference;

class ObjectStreamClass$FieldReflectorKey extends WeakReference {
    private final String sigs;
    private final int hash;
    private final boolean nullClass;
    
    ObjectStreamClass$FieldReflectorKey(Class cl, ObjectStreamField[] fields, ReferenceQueue queue) {
        super(cl, queue);
        nullClass = (cl == null);
        StringBuilder sbuf = new StringBuilder();
        for (int i = 0; i < fields.length; i++) {
            ObjectStreamField f = fields[i];
            sbuf.append(f.getName()).append(f.getSignature());
        }
        sigs = sbuf.toString();
        hash = System.identityHashCode(cl) + sigs.hashCode();
    }
    
    public int hashCode() {
        return hash;
    }
    
    public boolean equals(Object obj) {
        if (obj == this) {
            return true;
        }
        if (obj instanceof ObjectStreamClass$FieldReflectorKey) {
            ObjectStreamClass$FieldReflectorKey other = (ObjectStreamClass$FieldReflectorKey)(ObjectStreamClass$FieldReflectorKey)obj;
            Class referent;
            return (nullClass ? other.nullClass : ((referent = (Class)get()) != null) && (referent == other.get())) && sigs.equals(other.sigs);
        } else {
            return false;
        }
    }
}
