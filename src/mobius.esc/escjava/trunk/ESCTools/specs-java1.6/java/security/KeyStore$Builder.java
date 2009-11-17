package java.security;

import java.io.*;
import java.util.*;
import javax.security.auth.callback.*;

public abstract class KeyStore$Builder {
    
    protected KeyStore$Builder() {
        
    }
    
    public abstract KeyStore getKeyStore() throws KeyStoreException;
    
    public abstract KeyStore$ProtectionParameter getProtectionParameter(String alias) throws KeyStoreException;
    
    public static KeyStore$Builder newInstance(final KeyStore keyStore, final KeyStore$ProtectionParameter protectionParameter) {
        if ((keyStore == null) || (protectionParameter == null)) {
            throw new NullPointerException();
        }
        if (KeyStore.access$000(keyStore) == false) {
            throw new IllegalArgumentException("KeyStore not initialized");
        }
        return new KeyStore$Builder$1(keyStore, protectionParameter);
    }
    
    public static KeyStore$Builder newInstance(String type, Provider provider, File file, KeyStore$ProtectionParameter protection) {
        if ((type == null) || (file == null) || (protection == null)) {
            throw new NullPointerException();
        }
        if ((protection instanceof KeyStore$PasswordProtection == false) && (protection instanceof KeyStore$CallbackHandlerProtection == false)) {
            throw new IllegalArgumentException("Protection must be PasswordProtection or CallbackHandlerProtection");
        }
        if (file.isFile() == false) {
            throw new IllegalArgumentException("File does not exist or it does not refer " + "to a normal file: " + file);
        }
        return new KeyStore$Builder$FileBuilder(type, provider, file, protection, AccessController.getContext());
    }
    {
    }
    
    public static KeyStore$Builder newInstance(final String type, final Provider provider, final KeyStore$ProtectionParameter protection) {
        if ((type == null) || (protection == null)) {
            throw new NullPointerException();
        }
        final AccessControlContext context = AccessController.getContext();
        return new KeyStore$Builder$2(provider, type, protection);
    }
}
