package java.security.spec;

import java.math.BigInteger;

public class ECParameterSpec implements AlgorithmParameterSpec {
    private final EllipticCurve curve;
    private final ECPoint g;
    private final BigInteger n;
    private final int h;
    
    public ECParameterSpec(EllipticCurve curve, ECPoint g, BigInteger n, int h) {
        
        if (curve == null) {
            throw new NullPointerException("curve is null");
        }
        if (g == null) {
            throw new NullPointerException("g is null");
        }
        if (n == null) {
            throw new NullPointerException("n is null");
        }
        if (n.signum() != 1) {
            throw new IllegalArgumentException("n is not positive");
        }
        if (h <= 0) {
            throw new IllegalArgumentException("h is not positive");
        }
        this.curve = curve;
        this.g = g;
        this.n = n;
        this.h = h;
    }
    
    public EllipticCurve getCurve() {
        return curve;
    }
    
    public ECPoint getGenerator() {
        return g;
    }
    
    public BigInteger getOrder() {
        return n;
    }
    
    public int getCofactor() {
        return h;
    }
}
