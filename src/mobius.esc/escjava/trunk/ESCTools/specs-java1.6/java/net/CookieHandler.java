package java.net;

import java.util.Map;
import java.io.IOException;
import sun.security.util.SecurityConstants;

public abstract class CookieHandler {
    
    public CookieHandler() {
        
    }
    private static CookieHandler cookieHandler;
    
    public static synchronized CookieHandler getDefault() {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPermission(SecurityConstants.GET_COOKIEHANDLER_PERMISSION);
        }
        return cookieHandler;
    }
    
    public static synchronized void setDefault(CookieHandler cHandler) {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPermission(SecurityConstants.SET_COOKIEHANDLER_PERMISSION);
        }
        cookieHandler = cHandler;
    }
    
    public abstract Map get(URI uri, Map requestHeaders) throws IOException;
    
    public abstract void put(URI uri, Map responseHeaders) throws IOException;
}
