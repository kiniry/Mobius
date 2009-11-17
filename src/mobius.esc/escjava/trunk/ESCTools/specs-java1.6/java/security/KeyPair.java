package java.security;

import java.util.*;

public final class KeyPair implements java.io.Serializable {
    private static final long serialVersionUID = -7565189502268009837L;
    private PrivateKey privateKey;
    private PublicKey publicKey;
    
    public KeyPair(PublicKey publicKey, PrivateKey privateKey) {
        
        this.publicKey = publicKey;
        this.privateKey = privateKey;
    }
    
    public PublicKey getPublic() {
        return publicKey;
    }
    
    public PrivateKey getPrivate() {
        return privateKey;
    }
}
