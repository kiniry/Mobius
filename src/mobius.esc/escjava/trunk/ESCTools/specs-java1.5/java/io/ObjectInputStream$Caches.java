package java.io;

import java.lang.ref.ReferenceQueue;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;

class ObjectInputStream$Caches {
    
    private ObjectInputStream$Caches() {
        
    }
    static final ConcurrentMap subclassAudits = new ConcurrentHashMap();
    static final ReferenceQueue subclassAuditsQueue = new ReferenceQueue();
}
