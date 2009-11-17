package java.security.interfaces;

import java.security.*;

public interface DSAKeyPairGenerator {
    
    public void initialize(DSAParams params, SecureRandom random) throws InvalidParameterException;
    
    public void initialize(int modlen, boolean genParams, SecureRandom random) throws InvalidParameterException;
}
