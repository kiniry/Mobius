package java.security;

import java.io.*;


public abstract class Signer extends Identity {
    private static final long serialVersionUID = -1763464102261361480L;
    private PrivateKey privateKey;
    
    protected Signer() {
        
    }
    
    public Signer(String name) {
        super(name);
    }
    
    public Signer(String name, IdentityScope scope) throws KeyManagementException {
        super(name, scope);
    }
    
    public PrivateKey getPrivateKey() {
        check("getSignerPrivateKey");
        return privateKey;
    }
    
    public final void setKeyPair(KeyPair pair) throws InvalidParameterException, KeyException {
        check("setSignerKeyPair");
        final PublicKey pub = pair.getPublic();
        PrivateKey priv = pair.getPrivate();
        if (pub == null || priv == null) {
            throw new InvalidParameterException();
        }
        try {
            AccessController.doPrivileged(new Signer$1(this, pub));
        } catch (PrivilegedActionException pae) {
            throw (KeyManagementException)(KeyManagementException)pae.getException();
        }
        privateKey = priv;
    }
    
    String printKeys() {
        String keys = "";
        PublicKey publicKey = getPublicKey();
        if (publicKey != null && privateKey != null) {
            keys = "\tpublic and private keys initialized";
        } else {
            keys = "\tno keys";
        }
        return keys;
    }
    
    public String toString() {
        return "[Signer]" + super.toString();
    }
    
    private static void check(String directive) {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkSecurityAccess(directive);
        }
    }
}
