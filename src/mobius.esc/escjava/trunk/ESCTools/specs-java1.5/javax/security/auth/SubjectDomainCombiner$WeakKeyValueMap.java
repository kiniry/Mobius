package javax.security.auth;

import java.util.WeakHashMap;
import java.lang.ref.WeakReference;

class SubjectDomainCombiner$WeakKeyValueMap extends WeakHashMap {
    
    /*synthetic*/ SubjectDomainCombiner$WeakKeyValueMap(javax.security.auth.SubjectDomainCombiner$1 x0) {
        this();
    }
    
    private SubjectDomainCombiner$WeakKeyValueMap() {
        
    }
    
    public Object getValue(Object key) {
        WeakReference wr = (WeakReference)super.get(key);
        if (wr != null) {
            return wr.get();
        }
        return null;
    }
    
    public Object putValue(Object key, Object value) {
        WeakReference wr = (WeakReference)super.put(key, new WeakReference(value));
        if (wr != null) {
            return wr.get();
        }
        return null;
    }
}
