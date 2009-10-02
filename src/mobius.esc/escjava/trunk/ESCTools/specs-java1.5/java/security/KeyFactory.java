package java.security;

import java.util.*;
import java.security.Provider.Service;
import java.security.spec.KeySpec;
import java.security.spec.InvalidKeySpecException;
import sun.security.util.Debug;
import sun.security.jca.*;
import sun.security.jca.GetInstance.Instance;

public class KeyFactory {
    private static final Debug debug = Debug.getInstance("jca", "KeyFactory");
    private final String algorithm;
    private Provider provider;
    private volatile KeyFactorySpi spi;
    private final Object lock = new Object();
    private Iterator serviceIterator;
    
    protected KeyFactory(KeyFactorySpi keyFacSpi, Provider provider, String algorithm) {
        
        this.spi = keyFacSpi;
        this.provider = provider;
        this.algorithm = algorithm;
    }
    
    private KeyFactory(String algorithm) throws NoSuchAlgorithmException {
        
        this.algorithm = algorithm;
        List list = GetInstance.getServices("KeyFactory", algorithm);
        serviceIterator = list.iterator();
        if (nextSpi(null) == null) {
            throw new NoSuchAlgorithmException(algorithm + " KeyFactory not available");
        }
    }
    
    public static KeyFactory getInstance(String algorithm) throws NoSuchAlgorithmException {
        return new KeyFactory(algorithm);
    }
    
    public static KeyFactory getInstance(String algorithm, String provider) throws NoSuchAlgorithmException, NoSuchProviderException {
        GetInstance$Instance instance = GetInstance.getInstance("KeyFactory", KeyFactorySpi.class, algorithm, provider);
        return new KeyFactory((KeyFactorySpi)(KeyFactorySpi)instance.impl, instance.provider, algorithm);
    }
    
    public static KeyFactory getInstance(String algorithm, Provider provider) throws NoSuchAlgorithmException {
        GetInstance$Instance instance = GetInstance.getInstance("KeyFactory", KeyFactorySpi.class, algorithm, provider);
        return new KeyFactory((KeyFactorySpi)(KeyFactorySpi)instance.impl, instance.provider, algorithm);
    }
    
    public final Provider getProvider() {
        synchronized (lock) {
            serviceIterator = null;
            return provider;
        }
    }
    
    public final String getAlgorithm() {
        return this.algorithm;
    }
    
    private KeyFactorySpi nextSpi(KeyFactorySpi oldSpi) {
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
                    Object obj = s.newInstance(null);
                    if (obj instanceof KeyFactorySpi == false) {
                        continue;
                    }
                    KeyFactorySpi spi = (KeyFactorySpi)(KeyFactorySpi)obj;
                    provider = s.getProvider();
                    this.spi = spi;
                    return spi;
                } catch (NoSuchAlgorithmException e) {
                }
            }
            serviceIterator = null;
            return null;
        }
    }
    
    public final PublicKey generatePublic(KeySpec keySpec) throws InvalidKeySpecException {
        if (serviceIterator == null) {
            return spi.engineGeneratePublic(keySpec);
        }
        Exception failure = null;
        KeyFactorySpi mySpi = spi;
        do {
            try {
                return mySpi.engineGeneratePublic(keySpec);
            } catch (Exception e) {
                if (failure == null) {
                    failure = e;
                }
                mySpi = nextSpi(mySpi);
            }
        }         while (mySpi != null);
        if (failure instanceof RuntimeException) {
            throw (RuntimeException)(RuntimeException)failure;
        }
        if (failure instanceof InvalidKeySpecException) {
            throw (InvalidKeySpecException)(InvalidKeySpecException)failure;
        }
        throw new InvalidKeySpecException("Could not generate public key", failure);
    }
    
    public final PrivateKey generatePrivate(KeySpec keySpec) throws InvalidKeySpecException {
        if (serviceIterator == null) {
            return spi.engineGeneratePrivate(keySpec);
        }
        Exception failure = null;
        KeyFactorySpi mySpi = spi;
        do {
            try {
                return mySpi.engineGeneratePrivate(keySpec);
            } catch (Exception e) {
                if (failure == null) {
                    failure = e;
                }
                mySpi = nextSpi(mySpi);
            }
        }         while (mySpi != null);
        if (failure instanceof RuntimeException) {
            throw (RuntimeException)(RuntimeException)failure;
        }
        if (failure instanceof InvalidKeySpecException) {
            throw (InvalidKeySpecException)(InvalidKeySpecException)failure;
        }
        throw new InvalidKeySpecException("Could not generate private key", failure);
    }
    
    public final KeySpec getKeySpec(Key key, Class keySpec) throws InvalidKeySpecException {
        if (serviceIterator == null) {
            return spi.engineGetKeySpec(key, keySpec);
        }
        Exception failure = null;
        KeyFactorySpi mySpi = spi;
        do {
            try {
                return mySpi.engineGetKeySpec(key, keySpec);
            } catch (Exception e) {
                if (failure == null) {
                    failure = e;
                }
                mySpi = nextSpi(mySpi);
            }
        }         while (mySpi != null);
        if (failure instanceof RuntimeException) {
            throw (RuntimeException)(RuntimeException)failure;
        }
        if (failure instanceof InvalidKeySpecException) {
            throw (InvalidKeySpecException)(InvalidKeySpecException)failure;
        }
        throw new InvalidKeySpecException("Could not get key spec", failure);
    }
    
    public final Key translateKey(Key key) throws InvalidKeyException {
        if (serviceIterator == null) {
            return spi.engineTranslateKey(key);
        }
        Exception failure = null;
        KeyFactorySpi mySpi = spi;
        do {
            try {
                return mySpi.engineTranslateKey(key);
            } catch (Exception e) {
                if (failure == null) {
                    failure = e;
                }
                mySpi = nextSpi(mySpi);
            }
        }         while (mySpi != null);
        if (failure instanceof RuntimeException) {
            throw (RuntimeException)(RuntimeException)failure;
        }
        if (failure instanceof InvalidKeyException) {
            throw (InvalidKeyException)(InvalidKeyException)failure;
        }
        throw new InvalidKeyException("Could not translate key", failure);
    }
}
