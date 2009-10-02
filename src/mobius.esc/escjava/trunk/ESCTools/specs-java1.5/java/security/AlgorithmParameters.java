package java.security;

import java.io.*;
import java.security.spec.AlgorithmParameterSpec;
import java.security.spec.InvalidParameterSpecException;

public class AlgorithmParameters {
    private Provider provider;
    private AlgorithmParametersSpi paramSpi;
    private String algorithm;
    private boolean initialized = false;
    
    protected AlgorithmParameters(AlgorithmParametersSpi paramSpi, Provider provider, String algorithm) {
        
        this.paramSpi = paramSpi;
        this.provider = provider;
        this.algorithm = algorithm;
    }
    
    public final String getAlgorithm() {
        return this.algorithm;
    }
    
    public static AlgorithmParameters getInstance(String algorithm) throws NoSuchAlgorithmException {
        try {
            Object[] objs = Security.getImpl(algorithm, "AlgorithmParameters", (String)null);
            return new AlgorithmParameters((AlgorithmParametersSpi)(AlgorithmParametersSpi)objs[0], (Provider)(Provider)objs[1], algorithm);
        } catch (NoSuchProviderException e) {
            throw new NoSuchAlgorithmException(algorithm + " not found");
        }
    }
    
    public static AlgorithmParameters getInstance(String algorithm, String provider) throws NoSuchAlgorithmException, NoSuchProviderException {
        if (provider == null || provider.length() == 0) throw new IllegalArgumentException("missing provider");
        Object[] objs = Security.getImpl(algorithm, "AlgorithmParameters", provider);
        return new AlgorithmParameters((AlgorithmParametersSpi)(AlgorithmParametersSpi)objs[0], (Provider)(Provider)objs[1], algorithm);
    }
    
    public static AlgorithmParameters getInstance(String algorithm, Provider provider) throws NoSuchAlgorithmException {
        if (provider == null) throw new IllegalArgumentException("missing provider");
        Object[] objs = Security.getImpl(algorithm, "AlgorithmParameters", provider);
        return new AlgorithmParameters((AlgorithmParametersSpi)(AlgorithmParametersSpi)objs[0], (Provider)(Provider)objs[1], algorithm);
    }
    
    public final Provider getProvider() {
        return this.provider;
    }
    
    public final void init(AlgorithmParameterSpec paramSpec) throws InvalidParameterSpecException {
        if (this.initialized) throw new InvalidParameterSpecException("already initialized");
        paramSpi.engineInit(paramSpec);
        this.initialized = true;
    }
    
    public final void init(byte[] params) throws IOException {
        if (this.initialized) throw new IOException("already initialized");
        paramSpi.engineInit(params);
        this.initialized = true;
    }
    
    public final void init(byte[] params, String format) throws IOException {
        if (this.initialized) throw new IOException("already initialized");
        paramSpi.engineInit(params, format);
        this.initialized = true;
    }
    
    public final AlgorithmParameterSpec getParameterSpec(Class paramSpec) throws InvalidParameterSpecException {
        if (this.initialized == false) {
            throw new InvalidParameterSpecException("not initialized");
        }
        return paramSpi.engineGetParameterSpec(paramSpec);
    }
    
    public final byte[] getEncoded() throws IOException {
        if (this.initialized == false) {
            throw new IOException("not initialized");
        }
        return paramSpi.engineGetEncoded();
    }
    
    public final byte[] getEncoded(String format) throws IOException {
        if (this.initialized == false) {
            throw new IOException("not initialized");
        }
        return paramSpi.engineGetEncoded(format);
    }
    
    public final String toString() {
        if (this.initialized == false) {
            return null;
        }
        return paramSpi.engineToString();
    }
}
