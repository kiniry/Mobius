package java.net;

class SocksSocketImpl$5 implements java.security.PrivilegedAction {
    /*synthetic*/ final SocksSocketImpl this$0;
    
    SocksSocketImpl$5(/*synthetic*/ final SocksSocketImpl this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        return ProxySelector.getDefault();
    }
}
