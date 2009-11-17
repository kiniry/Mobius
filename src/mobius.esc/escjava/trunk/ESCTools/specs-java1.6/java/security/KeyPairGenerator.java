package java.security;

import java.util.*;
import java.security.spec.AlgorithmParameterSpec;
import java.security.Provider.Service;
import sun.security.jca.*;
import sun.security.jca.GetInstance.Instance;

public abstract class KeyPairGenerator extends KeyPairGeneratorSpi {
    private final String algorithm;
    Provider provider;
    
    protected KeyPairGenerator(String algorithm) {
        
        this.algorithm = algorithm;
    }
    
    public String getAlgorithm() {
        return this.algorithm;
    }
    
    private static KeyPairGenerator getInstance(GetInstance$Instance instance, String algorithm) {
        KeyPairGenerator kpg;
        if (instance.impl instanceof KeyPairGenerator) {
            kpg = (KeyPairGenerator)(KeyPairGenerator)instance.impl;
        } else {
            KeyPairGeneratorSpi spi = (KeyPairGeneratorSpi)(KeyPairGeneratorSpi)instance.impl;
            kpg = new KeyPairGenerator$Delegate(spi, algorithm);
        }
        kpg.provider = instance.provider;
        return kpg;
    }
    
    public static KeyPairGenerator getInstance(String algorithm) throws NoSuchAlgorithmException {
        List list = GetInstance.getServices("KeyPairGenerator", algorithm);
        Iterator t = list.iterator();
        if (t.hasNext() == false) {
            throw new NoSuchAlgorithmException(algorithm + " KeyPairGenerator not available");
        }
        NoSuchAlgorithmException failure = null;
        do {
            Provider$Service s = (Provider$Service)t.next();
            try {
                GetInstance$Instance instance = GetInstance.getInstance(s, KeyPairGeneratorSpi.class);
                if (instance.impl instanceof KeyPairGenerator) {
                    return getInstance(instance, algorithm);
                } else {
                    return new KeyPairGenerator$Delegate(instance, t, algorithm);
                }
            } catch (NoSuchAlgorithmException e) {
                if (failure == null) {
                    failure = e;
                }
            }
        }         while (t.hasNext());
        throw failure;
    }
    
    public static KeyPairGenerator getInstance(String algorithm, String provider) throws NoSuchAlgorithmException, NoSuchProviderException {
        GetInstance$Instance instance = GetInstance.getInstance("KeyPairGenerator", KeyPairGeneratorSpi.class, algorithm, provider);
        return getInstance(instance, algorithm);
    }
    
    public static KeyPairGenerator getInstance(String algorithm, Provider provider) throws NoSuchAlgorithmException {
        GetInstance$Instance instance = GetInstance.getInstance("KeyPairGenerator", KeyPairGeneratorSpi.class, algorithm, provider);
        return getInstance(instance, algorithm);
    }
    
    public final Provider getProvider() {
        disableFailover();
        return this.provider;
    }
    
    void disableFailover() {
    }
    
    public void initialize(int keysize) {
        initialize(keysize, JCAUtil.getSecureRandom());
    }
    
    public void initialize(int keysize, SecureRandom random) {
    }
    
    public void initialize(AlgorithmParameterSpec params) throws InvalidAlgorithmParameterException {
        initialize(params, JCAUtil.getSecureRandom());
    }
    
    public void initialize(AlgorithmParameterSpec params, SecureRandom random) throws InvalidAlgorithmParameterException {
    }
    
    public final KeyPair genKeyPair() {
        return generateKeyPair();
    }
    
    public KeyPair generateKeyPair() {
        return null;
    }
    {
    }
}
