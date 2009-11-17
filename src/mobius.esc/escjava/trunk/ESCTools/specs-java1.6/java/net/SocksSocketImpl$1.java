package java.net;

import java.io.IOException;

class SocksSocketImpl$1 implements java.security.PrivilegedExceptionAction {
    /*synthetic*/ final SocksSocketImpl this$0;
    /*synthetic*/ final int val$timeout;
    /*synthetic*/ final int val$port;
    /*synthetic*/ final String val$host;
    
    SocksSocketImpl$1(/*synthetic*/ final SocksSocketImpl this$0, /*synthetic*/ final String val$host, /*synthetic*/ final int val$port, /*synthetic*/ final int val$timeout) throws IOException {
        this.this$0 = this$0;
        this.val$host = val$host;
        this.val$port = val$port;
        this.val$timeout = val$timeout;
        
    }
    
    public Object run() throws IOException {
        SocksSocketImpl.access$000(this$0, val$host, val$port, val$timeout);
        SocksSocketImpl.access$102(this$0, this$0.getInputStream());
        SocksSocketImpl.access$202(this$0, this$0.getOutputStream());
        return null;
    }
}
