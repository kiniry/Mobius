package java.security.cert;

import java.io.InputStream;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;

public abstract class CertificateFactorySpi {
    
    public CertificateFactorySpi() {
        
    }
    
    public abstract Certificate engineGenerateCertificate(InputStream inStream) throws CertificateException;
    
    public CertPath engineGenerateCertPath(InputStream inStream) throws CertificateException {
        throw new UnsupportedOperationException();
    }
    
    public CertPath engineGenerateCertPath(InputStream inStream, String encoding) throws CertificateException {
        throw new UnsupportedOperationException();
    }
    
    public CertPath engineGenerateCertPath(List certificates) throws CertificateException {
        throw new UnsupportedOperationException();
    }
    
    public Iterator engineGetCertPathEncodings() {
        throw new UnsupportedOperationException();
    }
    
    public abstract Collection engineGenerateCertificates(InputStream inStream) throws CertificateException;
    
    public abstract CRL engineGenerateCRL(InputStream inStream) throws CRLException;
    
    public abstract Collection engineGenerateCRLs(InputStream inStream) throws CRLException;
}
