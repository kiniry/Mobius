package java.security;

import java.io.*;
import java.security.cert.CertificateException;
import java.util.*;
import javax.security.auth.callback.*;

class KeyStore$Builder$FileBuilder$1 implements PrivilegedExceptionAction {
    /*synthetic*/ final KeyStore$Builder$FileBuilder this$0;
    
    KeyStore$Builder$FileBuilder$1(/*synthetic*/ final KeyStore$Builder$FileBuilder this$0) throws UnsupportedCallbackException, KeyStoreException, NoSuchAlgorithmException, CertificateException, IOException {
        this.this$0 = this$0;
        
    }
    
    public Object run() throws Exception {
        KeyStore ks;
        if (KeyStore.Builder.FileBuilder.access$100(this$0) == null) {
            ks = KeyStore.getInstance(KeyStore.Builder.FileBuilder.access$200(this$0));
        } else {
            ks = KeyStore.getInstance(KeyStore.Builder.FileBuilder.access$200(this$0), KeyStore.Builder.FileBuilder.access$100(this$0));
        }
        InputStream in = null;
        char[] password = null;
        try {
            in = new FileInputStream(KeyStore.Builder.FileBuilder.access$300(this$0));
            if (KeyStore.Builder.FileBuilder.access$400(this$0) instanceof KeyStore$PasswordProtection) {
                password = ((KeyStore$PasswordProtection)(KeyStore$PasswordProtection)KeyStore.Builder.FileBuilder.access$400(this$0)).getPassword();
            } else {
                CallbackHandler handler = ((KeyStore$CallbackHandlerProtection)(KeyStore$CallbackHandlerProtection)KeyStore.Builder.FileBuilder.access$400(this$0)).getCallbackHandler();
                PasswordCallback callback = new PasswordCallback("Password for keystore " + KeyStore.Builder.FileBuilder.access$300(this$0).getName(), false);
                handler.handle(new Callback[]{callback});
                password = callback.getPassword();
                if (password == null) {
                    throw new KeyStoreException("No password provided");
                }
                callback.clearPassword();
                KeyStore.Builder.FileBuilder.access$402(this$0, new KeyStore$PasswordProtection(password));
            }
            ks.load(in, password);
            return ks;
        } finally {
            if (in != null) {
                in.close();
            }
        }
    }
}
