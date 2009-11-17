package java.security.interfaces;

import java.math.BigInteger;

public interface DSAPublicKey extends DSAKey, java.security.PublicKey {
    static final long serialVersionUID = 1234526332779022332L;
    
    public BigInteger getY();
}
