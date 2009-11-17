package java.security;

import java.io.*;

class Signer$1 implements PrivilegedExceptionAction {
    /*synthetic*/ final Signer this$0;
    /*synthetic*/ final PublicKey val$pub;
    
    Signer$1(/*synthetic*/ final Signer this$0, /*synthetic*/ final PublicKey val$pub) throws KeyManagementException {
        this.this$0 = this$0;
        this.val$pub = val$pub;
        
    }
    
    public Object run() throws KeyManagementException {
        this$0.setPublicKey(val$pub);
        return null;
    }
}
