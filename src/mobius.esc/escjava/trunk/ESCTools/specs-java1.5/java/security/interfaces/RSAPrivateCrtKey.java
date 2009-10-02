package java.security.interfaces;

import java.math.BigInteger;

public interface RSAPrivateCrtKey extends RSAPrivateKey {
    static final long serialVersionUID = -5682214253527700368L;
    
    public BigInteger getPublicExponent();
    
    public BigInteger getPrimeP();
    
    public BigInteger getPrimeQ();
    
    public BigInteger getPrimeExponentP();
    
    public BigInteger getPrimeExponentQ();
    
    public BigInteger getCrtCoefficient();
}
