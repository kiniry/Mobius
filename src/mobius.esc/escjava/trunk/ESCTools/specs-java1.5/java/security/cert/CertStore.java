package java.security.cert;

import java.security.AccessController;
import java.security.InvalidAlgorithmParameterException;
import java.security.NoSuchAlgorithmException;
import java.security.NoSuchProviderException;
import java.security.Provider;
import java.util.Collection;
import sun.security.jca.*;
import sun.security.jca.GetInstance.Instance;

public class CertStore {
    private static final String CERTSTORE_TYPE = "certstore.type";
    private CertStoreSpi storeSpi;
    private Provider provider;
    private String type;
    private CertStoreParameters params;
    
    protected CertStore(CertStoreSpi storeSpi, Provider provider, String type, CertStoreParameters params) {
        
        this.storeSpi = storeSpi;
        this.provider = provider;
        this.type = type;
        if (params != null) this.params = (CertStoreParameters)(CertStoreParameters)params.clone();
    }
    
    public final Collection getCertificates(CertSelector selector) throws CertStoreException {
        return storeSpi.engineGetCertificates(selector);
    }
    
    public final Collection getCRLs(CRLSelector selector) throws CertStoreException {
        return storeSpi.engineGetCRLs(selector);
    }
    
    public static CertStore getInstance(String type, CertStoreParameters params) throws InvalidAlgorithmParameterException, NoSuchAlgorithmException {
        try {
            GetInstance$Instance instance = GetInstance.getInstance("CertStore", CertStoreSpi.class, type, params);
            return new CertStore((CertStoreSpi)(CertStoreSpi)instance.impl, instance.provider, type, params);
        } catch (NoSuchAlgorithmException e) {
            return handleException(e);
        }
    }
    
    private static CertStore handleException(NoSuchAlgorithmException e) throws NoSuchAlgorithmException, InvalidAlgorithmParameterException {
        Throwable cause = e.getCause();
        if (cause instanceof InvalidAlgorithmParameterException) {
            throw (InvalidAlgorithmParameterException)(InvalidAlgorithmParameterException)cause;
        }
        throw e;
    }
    
    public static CertStore getInstance(String type, CertStoreParameters params, String provider) throws InvalidAlgorithmParameterException, NoSuchAlgorithmException, NoSuchProviderException {
        try {
            GetInstance$Instance instance = GetInstance.getInstance("CertStore", CertStoreSpi.class, type, params, provider);
            return new CertStore((CertStoreSpi)(CertStoreSpi)instance.impl, instance.provider, type, params);
        } catch (NoSuchAlgorithmException e) {
            return handleException(e);
        }
    }
    
    public static CertStore getInstance(String type, CertStoreParameters params, Provider provider) throws NoSuchAlgorithmException, InvalidAlgorithmParameterException {
        try {
            GetInstance$Instance instance = GetInstance.getInstance("CertStore", CertStoreSpi.class, type, params, provider);
            return new CertStore((CertStoreSpi)(CertStoreSpi)instance.impl, instance.provider, type, params);
        } catch (NoSuchAlgorithmException e) {
            return handleException(e);
        }
    }
    
    public final CertStoreParameters getCertStoreParameters() {
        return (params == null ? null : (CertStoreParameters)(CertStoreParameters)params.clone());
    }
    
    public final String getType() {
        return this.type;
    }
    
    public final Provider getProvider() {
        return this.provider;
    }
    
    public static final String getDefaultType() {
        String cstype;
        cstype = (String)(String)AccessController.doPrivileged(new CertStore$1());
        if (cstype == null) {
            cstype = "LDAP";
        }
        return cstype;
    }
}
