package java.net;

import java.io.IOException;
import java.security.PrivilegedExceptionAction;

class Socket$3 implements PrivilegedExceptionAction {
    /*synthetic*/ final Socket this$0;
    
    Socket$3(/*synthetic*/ final Socket this$0) throws IOException {
        this.this$0 = this$0;
        
    }
    
    public Object run() throws IOException {
        return this$0.impl.getOutputStream();
    }
}
