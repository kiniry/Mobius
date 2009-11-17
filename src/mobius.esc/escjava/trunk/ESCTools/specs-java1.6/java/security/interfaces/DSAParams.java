package java.security.interfaces;

import java.math.BigInteger;

public interface DSAParams {
    
    public BigInteger getP();
    
    public BigInteger getQ();
    
    public BigInteger getG();
}
