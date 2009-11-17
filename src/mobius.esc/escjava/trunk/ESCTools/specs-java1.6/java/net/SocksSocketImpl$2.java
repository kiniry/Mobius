package java.net;

class SocksSocketImpl$2 implements java.security.PrivilegedAction {
    /*synthetic*/ final SocksSocketImpl this$0;
    /*synthetic*/ final InetAddress val$addr;
    
    SocksSocketImpl$2(/*synthetic*/ final SocksSocketImpl this$0, /*synthetic*/ final InetAddress val$addr) {
        this.this$0 = this$0;
        this.val$addr = val$addr;
        
    }
    
    public Object run() {
        return Authenticator.requestPasswordAuthentication(SocksSocketImpl.access$300(this$0), val$addr, SocksSocketImpl.access$400(this$0), "SOCKS5", "SOCKS authentication", null);
    }
}
