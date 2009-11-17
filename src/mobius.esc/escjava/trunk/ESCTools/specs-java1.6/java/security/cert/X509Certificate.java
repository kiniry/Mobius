package java.security.cert;

import java.math.BigInteger;
import java.security.Principal;
import java.util.Collection;
import java.util.Date;
import java.util.List;
import javax.security.auth.x500.X500Principal;
import sun.security.x509.X509CertImpl;

public abstract class X509Certificate extends Certificate implements X509Extension {
    private static final long serialVersionUID = -2491127588187038216L;
    private transient X500Principal subjectX500Principal;
    private transient X500Principal issuerX500Principal;
    
    protected X509Certificate() {
        super("X.509");
    }
    
    public abstract void checkValidity() throws CertificateExpiredException, CertificateNotYetValidException;
    
    public abstract void checkValidity(Date date) throws CertificateExpiredException, CertificateNotYetValidException;
    
    public abstract int getVersion();
    
    public abstract BigInteger getSerialNumber();
    
    public abstract Principal getIssuerDN();
    
    public X500Principal getIssuerX500Principal() {
        if (issuerX500Principal == null) {
            issuerX500Principal = X509CertImpl.getIssuerX500Principal(this);
        }
        return issuerX500Principal;
    }
    
    public abstract Principal getSubjectDN();
    
    public X500Principal getSubjectX500Principal() {
        if (subjectX500Principal == null) {
            subjectX500Principal = X509CertImpl.getSubjectX500Principal(this);
        }
        return subjectX500Principal;
    }
    
    public abstract Date getNotBefore();
    
    public abstract Date getNotAfter();
    
    public abstract byte[] getTBSCertificate() throws CertificateEncodingException;
    
    public abstract byte[] getSignature();
    
    public abstract String getSigAlgName();
    
    public abstract String getSigAlgOID();
    
    public abstract byte[] getSigAlgParams();
    
    public abstract boolean[] getIssuerUniqueID();
    
    public abstract boolean[] getSubjectUniqueID();
    
    public abstract boolean[] getKeyUsage();
    
    public List getExtendedKeyUsage() throws CertificateParsingException {
        return X509CertImpl.getExtendedKeyUsage(this);
    }
    
    public abstract int getBasicConstraints();
    
    public Collection getSubjectAlternativeNames() throws CertificateParsingException {
        return X509CertImpl.getSubjectAlternativeNames(this);
    }
    
    public Collection getIssuerAlternativeNames() throws CertificateParsingException {
        return X509CertImpl.getIssuerAlternativeNames(this);
    }
}
