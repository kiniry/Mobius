package java.security;

import java.security.spec.AlgorithmParameterSpec;

public abstract class KeyPairGeneratorSpi {
    
    public KeyPairGeneratorSpi() {
        
    }
    
    public abstract void initialize(int keysize, SecureRandom random);
    
    public void initialize(AlgorithmParameterSpec params, SecureRandom random) throws InvalidAlgorithmParameterException {
        throw new UnsupportedOperationException();
    }
    
    public abstract KeyPair generateKeyPair();
}
