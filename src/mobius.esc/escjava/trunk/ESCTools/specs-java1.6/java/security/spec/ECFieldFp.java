package java.security.spec;

import java.math.BigInteger;

public class ECFieldFp implements ECField {
    private BigInteger p;
    
    public ECFieldFp(BigInteger p) {
        
        if (p.signum() != 1) {
            throw new IllegalArgumentException("p is not positive");
        }
        this.p = p;
    }
    
    public int getFieldSize() {
        return p.bitLength();
    }
    {
    }
    
    public BigInteger getP() {
        return p;
    }
    
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj instanceof ECFieldFp) {
            return (p.equals(((ECFieldFp)(ECFieldFp)obj).p));
        }
        return false;
    }
    
    public int hashCode() {
        return p.hashCode();
    }
}
