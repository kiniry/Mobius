package java.util;

import java.lang.ref.ReferenceQueue;
import java.lang.ref.WeakReference;

final class ResourceBundle$LoaderReference extends WeakReference {
    private ResourceBundle$ResourceCacheKey cacheKey;
    
    ResourceBundle$LoaderReference(Object referent, ReferenceQueue q, ResourceBundle$ResourceCacheKey key) {
        super(referent, q);
        cacheKey = key;
    }
    
    ResourceBundle$ResourceCacheKey getCacheKey() {
        return cacheKey;
    }
}
