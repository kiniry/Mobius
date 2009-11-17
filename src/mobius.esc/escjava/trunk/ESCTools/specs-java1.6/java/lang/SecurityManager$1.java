package java.lang;

import java.security.*;
import java.lang.reflect.*;

class SecurityManager$1 implements PrivilegedAction {
    /*synthetic*/ final SecurityManager this$0;
    
    SecurityManager$1(/*synthetic*/ final SecurityManager this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        return java.security.Security.getProperty("package.access");
    }
}
