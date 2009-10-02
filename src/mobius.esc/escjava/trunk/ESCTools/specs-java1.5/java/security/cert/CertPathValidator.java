package java.security.cert;

import java.security.AccessController;
import java.security.InvalidAlgorithmParameterException;
import java.security.NoSuchAlgorithmException;
import java.security.NoSuchProviderException;
import java.security.Provider;
import sun.security.util.Debug;
import sun.security.jca.*;
import sun.security.jca.GetInstance.Instance;

public class CertPathValidator {
    private static final String CPV_TYPE = "certpathvalidator.type";
    private static final Debug debug = Debug.getInstance("certpath");
    private CertPathValidatorSpi validatorSpi;
    private Provider provider;
    private String algorithm;
    
    protected CertPathValidator(CertPathValidatorSpi validatorSpi, Provider provider, String algorithm) {
        
        this.validatorSpi = validatorSpi;
        this.provider = provider;
        this.algorithm = algorithm;
    }
    
    public static CertPathValidator getInstance(String algorithm) throws NoSuchAlgorithmException {
        GetInstance$Instance instance = GetInstance.getInstance("CertPathValidator", CertPathValidatorSpi.class, algorithm);
        return new CertPathValidator((CertPathValidatorSpi)(CertPathValidatorSpi)instance.impl, instance.provider, algorithm);
    }
    
    public static CertPathValidator getInstance(String algorithm, String provider) throws NoSuchAlgorithmException, NoSuchProviderException {
        GetInstance$Instance instance = GetInstance.getInstance("CertPathValidator", CertPathValidatorSpi.class, algorithm, provider);
        return new CertPathValidator((CertPathValidatorSpi)(CertPathValidatorSpi)instance.impl, instance.provider, algorithm);
    }
    
    public static CertPathValidator getInstance(String algorithm, Provider provider) throws NoSuchAlgorithmException {
        GetInstance$Instance instance = GetInstance.getInstance("CertPathValidator", CertPathValidatorSpi.class, algorithm, provider);
        return new CertPathValidator((CertPathValidatorSpi)(CertPathValidatorSpi)instance.impl, instance.provider, algorithm);
    }
    
    public final Provider getProvider() {
        return this.provider;
    }
    
    public final String getAlgorithm() {
        return this.algorithm;
    }
    
    public final CertPathValidatorResult validate(CertPath certPath, CertPathParameters params) throws CertPathValidatorException, InvalidAlgorithmParameterException {
        return validatorSpi.engineValidate(certPath, params);
    }
    
    public static final String getDefaultType() {
        String cpvtype;
        cpvtype = (String)(String)AccessController.doPrivileged(new CertPathValidator$1());
        if (cpvtype == null) {
            cpvtype = "PKIX";
        }
        return cpvtype;
    }
}
