package java.net;

import java.io.IOException;
import java.util.Map;
import sun.security.util.SecurityConstants;

public abstract class ResponseCache {
    
    public ResponseCache() {
        
    }
    private static ResponseCache theResponseCache;
    
    public static synchronized ResponseCache getDefault() {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPermission(SecurityConstants.GET_RESPONSECACHE_PERMISSION);
        }
        return theResponseCache;
    }
    
    public static synchronized void setDefault(ResponseCache responseCache) {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPermission(SecurityConstants.SET_RESPONSECACHE_PERMISSION);
        }
        theResponseCache = responseCache;
    }
    
    public abstract CacheResponse get(URI uri, String rqstMethod, Map rqstHeaders) throws IOException;
    
    public abstract CacheRequest put(URI uri, URLConnection conn) throws IOException;
}
