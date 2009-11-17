package java.net;

import java.io.IOException;
import java.security.PrivilegedExceptionAction;

class SocksSocketImpl$7 implements PrivilegedExceptionAction {
    /*synthetic*/ final SocksSocketImpl this$0;
    
    SocksSocketImpl$7(/*synthetic*/ final SocksSocketImpl this$0) throws IOException {
        this.this$0 = this$0;
        
    }
    
    public Object run() throws Exception {
        SocksSocketImpl.access$502(this$0, new Socket(new PlainSocketImpl()));
        SocksSocketImpl.access$500(this$0).connect(new InetSocketAddress(SocksSocketImpl.access$300(this$0), SocksSocketImpl.access$400(this$0)));
        SocksSocketImpl.access$102(this$0, SocksSocketImpl.access$500(this$0).getInputStream());
        SocksSocketImpl.access$202(this$0, SocksSocketImpl.access$500(this$0).getOutputStream());
        return null;
    }
}
