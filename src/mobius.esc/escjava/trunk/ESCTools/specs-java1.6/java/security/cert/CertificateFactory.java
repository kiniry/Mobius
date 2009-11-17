package java.security.cert;

import java.io.InputStream;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.security.Provider;
import java.security.NoSuchAlgorithmException;
import java.security.NoSuchProviderException;
import sun.security.jca.*;
import sun.security.jca.GetInstance.Instance;

public class CertificateFactory {
    private String type;
    private Provider provider;
    private CertificateFactorySpi certFacSpi;
    
    protected CertificateFactory(CertificateFactorySpi certFacSpi, Provider provider, String type) {
        
        this.certFacSpi = certFacSpi;
        this.provider = provider;
        this.type = type;
    }
    
    public static final CertificateFactory getInstance(String type) throws CertificateException {
        try {
            GetInstance$Instance instance = GetInstance.getInstance("CertificateFactory", CertificateFactorySpi.class, type);
            return new CertificateFactory((CertificateFactorySpi)(CertificateFactorySpi)instance.impl, instance.provider, type);
        } catch (NoSuchAlgorithmException e) {
            throw new CertificateException(type + " not found", e);
        }
    }
    
    public static final CertificateFactory getInstance(String type, String provider) throws CertificateException, NoSuchProviderException {
        try {
            GetInstance$Instance instance = GetInstance.getInstance("CertificateFactory", CertificateFactorySpi.class, type, provider);
            return new CertificateFactory((CertificateFactorySpi)(CertificateFactorySpi)instance.impl, instance.provider, type);
        } catch (NoSuchAlgorithmException e) {
            throw new CertificateException(type + " not found", e);
        }
    }
    
    public static final CertificateFactory getInstance(String type, Provider provider) throws CertificateException {
        try {
            GetInstance$Instance instance = GetInstance.getInstance("CertificateFactory", CertificateFactorySpi.class, type, provider);
            return new CertificateFactory((CertificateFactorySpi)(CertificateFactorySpi)instance.impl, instance.provider, type);
        } catch (NoSuchAlgorithmException e) {
            throw new CertificateException(type + " not found", e);
        }
    }
    
    public final Provider getProvider() {
        return this.provider;
    }
    
    public final String getType() {
        return this.type;
    }
    
    public final Certificate generateCertificate(InputStream inStream) throws CertificateException {
        return certFacSpi.engineGenerateCertificate(inStream);
    }
    
    public final Iterator getCertPathEncodings() {
        return (certFacSpi.engineGetCertPathEncodings());
    }
    
    public final CertPath generateCertPath(InputStream inStream) throws CertificateException {
        return (certFacSpi.engineGenerateCertPath(inStream));
    }
    
    public final CertPath generateCertPath(InputStream inStream, String encoding) throws CertificateException {
        return (certFacSpi.engineGenerateCertPath(inStream, encoding));
    }
    
    public final CertPath generateCertPath(List certificates) throws CertificateException {
        return (certFacSpi.engineGenerateCertPath(certificates));
    }
    
    public final Collection generateCertificates(InputStream inStream) throws CertificateException {
        return certFacSpi.engineGenerateCertificates(inStream);
    }
    
    public final CRL generateCRL(InputStream inStream) throws CRLException {
        return certFacSpi.engineGenerateCRL(inStream);
    }
    
    public final Collection generateCRLs(InputStream inStream) throws CRLException {
        return certFacSpi.engineGenerateCRLs(inStream);
    }
}
