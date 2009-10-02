package java.security;

import java.util.*;
import java.security.spec.AlgorithmParameterSpec;
import java.security.Provider.Service;
import sun.security.jca.*;
import sun.security.jca.GetInstance.Instance;

final class KeyPairGenerator$Delegate extends KeyPairGenerator {
    private volatile KeyPairGeneratorSpi spi;
    private final Object lock = new Object();
    private Iterator serviceIterator;
    private static final int I_NONE = 1;
    private static final int I_SIZE = 2;
    private static final int I_PARAMS = 3;
    private int initType;
    private int initKeySize;
    private AlgorithmParameterSpec initParams;
    private SecureRandom initRandom;
    
    KeyPairGenerator$Delegate(KeyPairGeneratorSpi spi, String algorithm) {
        super(algorithm);
        this.spi = spi;
    }
    
    KeyPairGenerator$Delegate(GetInstance$Instance instance, Iterator serviceIterator, String algorithm) {
        super(algorithm);
        spi = (KeyPairGeneratorSpi)(KeyPairGeneratorSpi)instance.impl;
        provider = instance.provider;
        this.serviceIterator = serviceIterator;
        initType = I_NONE;
    }
    
    private KeyPairGeneratorSpi nextSpi(KeyPairGeneratorSpi oldSpi, boolean reinit) {
        synchronized (lock) {
            if ((oldSpi != null) && (oldSpi != spi)) {
                return spi;
            }
            if (serviceIterator == null) {
                return null;
            }
            while (serviceIterator.hasNext()) {
                Provider$Service s = (Provider$Service)serviceIterator.next();
                try {
                    Object inst = s.newInstance(null);
                    if (inst instanceof KeyPairGeneratorSpi == false) {
                        continue;
                    }
                    if (inst instanceof KeyPairGenerator) {
                        continue;
                    }
                    KeyPairGeneratorSpi spi = (KeyPairGeneratorSpi)(KeyPairGeneratorSpi)inst;
                    if (reinit) {
                        if (initType == I_SIZE) {
                            spi.initialize(initKeySize, initRandom);
                        } else if (initType == I_PARAMS) {
                            spi.initialize(initParams, initRandom);
                        } else if (initType != I_NONE) {
                            throw new AssertionError("KeyPairGenerator initType: " + initType);
                        }
                    }
                    provider = s.getProvider();
                    this.spi = spi;
                    return spi;
                } catch (Exception e) {
                }
            }
            disableFailover();
            return null;
        }
    }
    
    void disableFailover() {
        serviceIterator = null;
        initType = 0;
        initParams = null;
        initRandom = null;
    }
    
    public void initialize(int keysize, SecureRandom random) {
        if (serviceIterator == null) {
            spi.initialize(keysize, random);
            return;
        }
        RuntimeException failure = null;
        KeyPairGeneratorSpi mySpi = spi;
        do {
            try {
                mySpi.initialize(keysize, random);
                initType = I_SIZE;
                initKeySize = keysize;
                initParams = null;
                initRandom = random;
                return;
            } catch (RuntimeException e) {
                if (failure == null) {
                    failure = e;
                }
                mySpi = nextSpi(mySpi, false);
            }
        }         while (mySpi != null);
        throw failure;
    }
    
    public void initialize(AlgorithmParameterSpec params, SecureRandom random) throws InvalidAlgorithmParameterException {
        if (serviceIterator == null) {
            spi.initialize(params, random);
            return;
        }
        Exception failure = null;
        KeyPairGeneratorSpi mySpi = spi;
        do {
            try {
                mySpi.initialize(params, random);
                initType = I_PARAMS;
                initKeySize = 0;
                initParams = params;
                initRandom = random;
                return;
            } catch (Exception e) {
                if (failure == null) {
                    failure = e;
                }
                mySpi = nextSpi(mySpi, false);
            }
        }         while (mySpi != null);
        if (failure instanceof RuntimeException) {
            throw (RuntimeException)(RuntimeException)failure;
        }
        throw (InvalidAlgorithmParameterException)(InvalidAlgorithmParameterException)failure;
    }
    
    public KeyPair generateKeyPair() {
        if (serviceIterator == null) {
            return spi.generateKeyPair();
        }
        RuntimeException failure = null;
        KeyPairGeneratorSpi mySpi = spi;
        do {
            try {
                return mySpi.generateKeyPair();
            } catch (RuntimeException e) {
                if (failure == null) {
                    failure = e;
                }
                mySpi = nextSpi(mySpi, true);
            }
        }         while (mySpi != null);
        throw failure;
    }
}
