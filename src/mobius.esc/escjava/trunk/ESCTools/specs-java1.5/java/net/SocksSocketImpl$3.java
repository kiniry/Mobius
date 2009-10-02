package java.net;

import java.io.IOException;
import java.util.prefs.Preferences;

class SocksSocketImpl$3 implements java.security.PrivilegedExceptionAction {
    /*synthetic*/ final SocksSocketImpl this$0;
    /*synthetic*/ final Preferences val$prefs;
    
    SocksSocketImpl$3(/*synthetic*/ final SocksSocketImpl this$0, /*synthetic*/ final Preferences val$prefs) {
        this.this$0 = this$0;
        this.val$prefs = val$prefs;
        
    }
    
    public Object run() throws IOException {
        return val$prefs.get("username", null);
    }
}
