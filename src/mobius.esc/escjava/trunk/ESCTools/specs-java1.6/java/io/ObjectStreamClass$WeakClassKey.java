package java.io;

import java.lang.ref.ReferenceQueue;
import java.lang.ref.WeakReference;

class ObjectStreamClass$WeakClassKey extends WeakReference {
    private final int hash;
    
    ObjectStreamClass$WeakClassKey(Class cl, ReferenceQueue refQueue) {
        super(cl, refQueue);
        hash = System.identityHashCode(cl);
    }
    
    public int hashCode() {
        return hash;
    }
    
    public boolean equals(Object obj) {
        if (obj == this) {
            return true;
        }
        if (obj instanceof ObjectStreamClass$WeakClassKey) {
            Object referent = get();
            return (referent != null) && (referent == ((ObjectStreamClass$WeakClassKey)(ObjectStreamClass$WeakClassKey)obj).get());
        } else {
            return false;
        }
    }
}
