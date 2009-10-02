package java.security.spec;

import java.math.BigInteger;

public class DSAParameterSpec implements AlgorithmParameterSpec, java.security.interfaces.DSAParams {
    BigInteger p;
    BigInteger q;
    BigInteger g;
    
    public DSAParameterSpec(BigInteger p, BigInteger q, BigInteger g) {
        
        this.p = p;
        this.q = q;
        this.g = g;
    }
    
    public BigInteger getP() {
        return this.p;
    }
    
    public BigInteger getQ() {
        return this.q;
    }
    
    public BigInteger getG() {
        return this.g;
    }
}
