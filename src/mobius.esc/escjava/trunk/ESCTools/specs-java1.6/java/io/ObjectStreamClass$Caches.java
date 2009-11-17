package java.io;

import java.lang.ref.ReferenceQueue;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;

class ObjectStreamClass$Caches {
    
    /*synthetic*/ static ReferenceQueue access$2500() {
        return reflectorsQueue;
    }
    
    /*synthetic*/ static ReferenceQueue access$200() {
        return localDescsQueue;
    }
    
    private ObjectStreamClass$Caches() {
        
    }
    static final ConcurrentMap localDescs = new ConcurrentHashMap();
    static final ConcurrentMap reflectors = new ConcurrentHashMap();
    private static final ReferenceQueue localDescsQueue = new ReferenceQueue();
    private static final ReferenceQueue reflectorsQueue = new ReferenceQueue();
}
