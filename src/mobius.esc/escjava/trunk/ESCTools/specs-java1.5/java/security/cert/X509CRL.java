package java.security.cert;

import java.security.NoSuchAlgorithmException;
import java.security.NoSuchProviderException;
import java.security.InvalidKeyException;
import java.security.SignatureException;
import java.security.Principal;
import java.security.PublicKey;
import javax.security.auth.x500.X500Principal;
import java.math.BigInteger;
import java.util.Date;
import java.util.Set;
import java.util.Arrays;
import sun.security.x509.X509CRLImpl;

public abstract class X509CRL extends CRL implements X509Extension {
    private transient X500Principal issuerPrincipal;
    
    protected X509CRL() {
        super("X.509");
    }
    
    public boolean equals(Object other) {
        if (this == other) {
            return true;
        }
        if (!(other instanceof X509CRL)) {
            return false;
        }
        try {
            byte[] thisCRL = X509CRLImpl.getEncodedInternal(this);
            byte[] otherCRL = X509CRLImpl.getEncodedInternal((X509CRL)(X509CRL)other);
            return Arrays.equals(thisCRL, otherCRL);
        } catch (CRLException e) {
            return false;
        }
    }
    
    public int hashCode() {
        int retval = 0;
        try {
            byte[] crlData = X509CRLImpl.getEncodedInternal(this);
            for (int i = 1; i < crlData.length; i++) {
                retval += crlData[i] * i;
            }
            return retval;
        } catch (CRLException e) {
            return retval;
        }
    }
    
    public abstract byte[] getEncoded() throws CRLException;
    
    public abstract void verify(PublicKey key) throws CRLException, NoSuchAlgorithmException, InvalidKeyException, NoSuchProviderException, SignatureException;
    
    public abstract void verify(PublicKey key, String sigProvider) throws CRLException, NoSuchAlgorithmException, InvalidKeyException, NoSuchProviderException, SignatureException;
    
    public abstract int getVersion();
    
    public abstract Principal getIssuerDN();
    
    public X500Principal getIssuerX500Principal() {
        if (issuerPrincipal == null) {
            issuerPrincipal = X509CRLImpl.getIssuerX500Principal(this);
        }
        return issuerPrincipal;
    }
    
    public abstract Date getThisUpdate();
    
    public abstract Date getNextUpdate();
    
    public abstract X509CRLEntry getRevokedCertificate(BigInteger serialNumber);
    
    public X509CRLEntry getRevokedCertificate(X509Certificate certificate) {
        X500Principal certIssuer = certificate.getIssuerX500Principal();
        X500Principal crlIssuer = getIssuerX500Principal();
        if (certIssuer.equals(crlIssuer) == false) {
            return null;
        }
        return getRevokedCertificate(certificate.getSerialNumber());
    }
    
    public abstract Set getRevokedCertificates();
    
    public abstract byte[] getTBSCertList() throws CRLException;
    
    public abstract byte[] getSignature();
    
    public abstract String getSigAlgName();
    
    public abstract String getSigAlgOID();
    
    public abstract byte[] getSigAlgParams();
}
