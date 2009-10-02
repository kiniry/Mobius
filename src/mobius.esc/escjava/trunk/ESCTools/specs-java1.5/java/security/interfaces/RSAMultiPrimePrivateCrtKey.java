package java.security.interfaces;

import java.math.BigInteger;
import java.security.spec.RSAOtherPrimeInfo;

public interface RSAMultiPrimePrivateCrtKey extends RSAPrivateKey {
    static final long serialVersionUID = 618058533534628008L;
    
    public BigInteger getPublicExponent();
    
    public BigInteger getPrimeP();
    
    public BigInteger getPrimeQ();
    
    public BigInteger getPrimeExponentP();
    
    public BigInteger getPrimeExponentQ();
    
    public BigInteger getCrtCoefficient();
    
    public RSAOtherPrimeInfo[] getOtherPrimeInfo();
}
