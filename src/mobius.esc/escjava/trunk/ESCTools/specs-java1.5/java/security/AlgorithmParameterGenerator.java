package java.security;

import java.security.spec.AlgorithmParameterSpec;

public class AlgorithmParameterGenerator {
    private Provider provider;
    private AlgorithmParameterGeneratorSpi paramGenSpi;
    private String algorithm;
    
    protected AlgorithmParameterGenerator(AlgorithmParameterGeneratorSpi paramGenSpi, Provider provider, String algorithm) {
        
        this.paramGenSpi = paramGenSpi;
        this.provider = provider;
        this.algorithm = algorithm;
    }
    
    public final String getAlgorithm() {
        return this.algorithm;
    }
    
    public static AlgorithmParameterGenerator getInstance(String algorithm) throws NoSuchAlgorithmException {
        try {
            Object[] objs = Security.getImpl(algorithm, "AlgorithmParameterGenerator", (String)null);
            return new AlgorithmParameterGenerator((AlgorithmParameterGeneratorSpi)(AlgorithmParameterGeneratorSpi)objs[0], (Provider)(Provider)objs[1], algorithm);
        } catch (NoSuchProviderException e) {
            throw new NoSuchAlgorithmException(algorithm + " not found");
        }
    }
    
    public static AlgorithmParameterGenerator getInstance(String algorithm, String provider) throws NoSuchAlgorithmException, NoSuchProviderException {
        if (provider == null || provider.length() == 0) throw new IllegalArgumentException("missing provider");
        Object[] objs = Security.getImpl(algorithm, "AlgorithmParameterGenerator", provider);
        return new AlgorithmParameterGenerator((AlgorithmParameterGeneratorSpi)(AlgorithmParameterGeneratorSpi)objs[0], (Provider)(Provider)objs[1], algorithm);
    }
    
    public static AlgorithmParameterGenerator getInstance(String algorithm, Provider provider) throws NoSuchAlgorithmException {
        if (provider == null) throw new IllegalArgumentException("missing provider");
        Object[] objs = Security.getImpl(algorithm, "AlgorithmParameterGenerator", provider);
        return new AlgorithmParameterGenerator((AlgorithmParameterGeneratorSpi)(AlgorithmParameterGeneratorSpi)objs[0], (Provider)(Provider)objs[1], algorithm);
    }
    
    public final Provider getProvider() {
        return this.provider;
    }
    
    public final void init(int size) {
        paramGenSpi.engineInit(size, new SecureRandom());
    }
    
    public final void init(int size, SecureRandom random) {
        paramGenSpi.engineInit(size, random);
    }
    
    public final void init(AlgorithmParameterSpec genParamSpec) throws InvalidAlgorithmParameterException {
        paramGenSpi.engineInit(genParamSpec, new SecureRandom());
    }
    
    public final void init(AlgorithmParameterSpec genParamSpec, SecureRandom random) throws InvalidAlgorithmParameterException {
        paramGenSpi.engineInit(genParamSpec, random);
    }
    
    public final AlgorithmParameters generateParameters() {
        return paramGenSpi.engineGenerateParameters();
    }
}
