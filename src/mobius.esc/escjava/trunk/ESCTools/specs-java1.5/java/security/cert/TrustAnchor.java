package java.security.cert;

import java.io.IOException;
import java.security.PublicKey;
import javax.security.auth.x500.X500Principal;
import sun.security.x509.NameConstraintsExtension;

public class TrustAnchor {
    static {
        CertPathHelperImpl.initialize();
    }
    private final PublicKey pubKey;
    private final String caName;
    private final X500Principal caPrincipal;
    private final X509Certificate trustedCert;
    private byte[] ncBytes;
    private NameConstraintsExtension nc;
    
    public TrustAnchor(X509Certificate trustedCert, byte[] nameConstraints) {
        
        if (trustedCert == null) throw new NullPointerException("the trustedCert parameter must be non-null");
        this.trustedCert = trustedCert;
        this.pubKey = null;
        this.caName = null;
        this.caPrincipal = null;
        setNameConstraints(nameConstraints);
    }
    
    public TrustAnchor(X500Principal caPrincipal, PublicKey pubKey, byte[] nameConstraints) {
        
        if ((caPrincipal == null) || (pubKey == null)) {
            throw new NullPointerException();
        }
        this.trustedCert = null;
        this.caPrincipal = caPrincipal;
        this.caName = caPrincipal.getName();
        this.pubKey = pubKey;
        setNameConstraints(nameConstraints);
    }
    
    public TrustAnchor(String caName, PublicKey pubKey, byte[] nameConstraints) {
        
        if (pubKey == null) throw new NullPointerException("the pubKey parameter must be non-null");
        if (caName == null) throw new NullPointerException("the caName parameter must be non-null");
        if (caName.length() == 0) throw new IllegalArgumentException("the caName parameter must be a non-empty String");
        this.caPrincipal = new X500Principal(caName);
        this.pubKey = pubKey;
        this.caName = caName;
        this.trustedCert = null;
        setNameConstraints(nameConstraints);
    }
    
    public final X509Certificate getTrustedCert() {
        return this.trustedCert;
    }
    
    public final X500Principal getCA() {
        return this.caPrincipal;
    }
    
    public final String getCAName() {
        return this.caName;
    }
    
    public final PublicKey getCAPublicKey() {
        return this.pubKey;
    }
    
    private void setNameConstraints(byte[] bytes) {
        if (bytes == null) {
            ncBytes = null;
            nc = null;
        } else {
            ncBytes = (byte[])(byte[])bytes.clone();
            try {
                nc = new NameConstraintsExtension(Boolean.FALSE, bytes);
            } catch (IOException ioe) {
                IllegalArgumentException iae = new IllegalArgumentException(ioe.getMessage());
                iae.initCause(ioe);
                throw iae;
            }
        }
    }
    
    public final byte[] getNameConstraints() {
        return (ncBytes == null ? null : (byte[])(byte[])ncBytes.clone());
    }
    
    public String toString() {
        StringBuffer sb = new StringBuffer();
        sb.append("[\n");
        if (pubKey != null) {
            sb.append("  Trusted CA Public Key: " + pubKey.toString() + "\n");
            sb.append("  Trusted CA Issuer Name: " + String.valueOf(caName) + "\n");
        } else {
            sb.append("  Trusted CA cert: " + trustedCert.toString() + "\n");
        }
        if (nc != null) sb.append("  Name Constraints: " + nc.toString() + "\n");
        return sb.toString();
    }
}
