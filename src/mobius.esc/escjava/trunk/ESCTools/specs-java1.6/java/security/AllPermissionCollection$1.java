package java.security;

import java.security.*;
import java.util.Enumeration;
import sun.security.util.SecurityConstants;

class AllPermissionCollection$1 implements Enumeration {
    /*synthetic*/ final AllPermissionCollection this$0;
    
    AllPermissionCollection$1(/*synthetic*/ final AllPermissionCollection this$0) {
        this.this$0 = this$0;
        
    }
    private boolean hasMore = AllPermissionCollection.access$000(this$0);
    
    public boolean hasMoreElements() {
        return hasMore;
    }
    
    public Object nextElement() {
        hasMore = false;
        return SecurityConstants.ALL_PERMISSION;
    }
}
