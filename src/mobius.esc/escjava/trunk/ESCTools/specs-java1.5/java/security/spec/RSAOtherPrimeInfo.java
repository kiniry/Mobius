package java.security.spec;

import java.math.BigInteger;

public class RSAOtherPrimeInfo {
    private BigInteger prime;
    private BigInteger primeExponent;
    private BigInteger crtCoefficient;
    
    public RSAOtherPrimeInfo(BigInteger prime, BigInteger primeExponent, BigInteger crtCoefficient) {
        
        if (prime == null) {
            throw new NullPointerException("the prime parameter must be non-null");
        }
        if (primeExponent == null) {
            throw new NullPointerException("the primeExponent parameter must be non-null");
        }
        if (crtCoefficient == null) {
            throw new NullPointerException("the crtCoefficient parameter must be non-null");
        }
        this.prime = prime;
        this.primeExponent = primeExponent;
        this.crtCoefficient = crtCoefficient;
    }
    
    public final BigInteger getPrime() {
        return this.prime;
    }
    
    public final BigInteger getExponent() {
        return this.primeExponent;
    }
    
    public final BigInteger getCrtCoefficient() {
        return this.crtCoefficient;
    }
}
