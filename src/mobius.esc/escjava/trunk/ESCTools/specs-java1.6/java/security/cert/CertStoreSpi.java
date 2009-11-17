package java.security.cert;

import java.security.InvalidAlgorithmParameterException;
import java.util.Collection;

public abstract class CertStoreSpi {
    
    public CertStoreSpi(CertStoreParameters params) throws InvalidAlgorithmParameterException {
        
    }
    
    public abstract Collection engineGetCertificates(CertSelector selector) throws CertStoreException;
    
    public abstract Collection engineGetCRLs(CRLSelector selector) throws CertStoreException;
}
