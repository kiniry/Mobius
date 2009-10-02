package java.security.cert;

import java.security.AccessController;
import java.security.InvalidAlgorithmParameterException;
import java.security.NoSuchAlgorithmException;
import java.security.NoSuchProviderException;
import java.security.Provider;
import sun.security.util.Debug;
import sun.security.jca.*;
import sun.security.jca.GetInstance.Instance;

public class CertPathBuilder {
    private static final String CPB_TYPE = "certpathbuilder.type";
    private static final Debug debug = Debug.getInstance("certpath");
    private CertPathBuilderSpi builderSpi;
    private Provider provider;
    private String algorithm;
    
    protected CertPathBuilder(CertPathBuilderSpi builderSpi, Provider provider, String algorithm) {
        
        this.builderSpi = builderSpi;
        this.provider = provider;
        this.algorithm = algorithm;
    }
    
    public static CertPathBuilder getInstance(String algorithm) throws NoSuchAlgorithmException {
        GetInstance$Instance instance = GetInstance.getInstance("CertPathBuilder", CertPathBuilderSpi.class, algorithm);
        return new CertPathBuilder((CertPathBuilderSpi)(CertPathBuilderSpi)instance.impl, instance.provider, algorithm);
    }
    
    public static CertPathBuilder getInstance(String algorithm, String provider) throws NoSuchAlgorithmException, NoSuchProviderException {
        GetInstance$Instance instance = GetInstance.getInstance("CertPathBuilder", CertPathBuilderSpi.class, algorithm, provider);
        return new CertPathBuilder((CertPathBuilderSpi)(CertPathBuilderSpi)instance.impl, instance.provider, algorithm);
    }
    
    public static CertPathBuilder getInstance(String algorithm, Provider provider) throws NoSuchAlgorithmException {
        GetInstance$Instance instance = GetInstance.getInstance("CertPathBuilder", CertPathBuilderSpi.class, algorithm, provider);
        return new CertPathBuilder((CertPathBuilderSpi)(CertPathBuilderSpi)instance.impl, instance.provider, algorithm);
    }
    
    public final Provider getProvider() {
        return this.provider;
    }
    
    public final String getAlgorithm() {
        return this.algorithm;
    }
    
    public final CertPathBuilderResult build(CertPathParameters params) throws CertPathBuilderException, InvalidAlgorithmParameterException {
        return builderSpi.engineBuild(params);
    }
    
    public static final String getDefaultType() {
        String cpbtype;
        cpbtype = (String)(String)AccessController.doPrivileged(new CertPathBuilder$1());
        if (cpbtype == null) {
            cpbtype = "PKIX";
        }
        return cpbtype;
    }
}
