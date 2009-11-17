package java.security;

import java.io.*;
import java.security.cert.CertificateException;
import java.util.*;
import javax.security.auth.callback.*;

class KeyStore$Builder$2$1 implements PrivilegedExceptionAction {
    /*synthetic*/ final KeyStore$Builder$2 this$0;
    
    KeyStore$Builder$2$1(/*synthetic*/ final KeyStore$Builder$2 this$0) throws CertificateException, NoSuchAlgorithmException, IOException, KeyStoreException {
        this.this$0 = this$0;
        
    }
    
    public Object run() throws Exception {
        KeyStore ks;
        if (this$0.val$provider == null) {
            ks = KeyStore.getInstance(this$0.val$type);
        } else {
            ks = KeyStore.getInstance(this$0.val$type, this$0.val$provider);
        }
        ks.load(new KeyStore$SimpleLoadStoreParameter(this$0.val$protection));
        java.security.KeyStore$Builder$2.access$502(this$0, true);
        return ks;
    }
}
