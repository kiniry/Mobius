package java.security.spec;

import java.math.BigInteger;

public class ECPrivateKeySpec implements KeySpec {
    private BigInteger s;
    private ECParameterSpec params;
    
    public ECPrivateKeySpec(BigInteger s, ECParameterSpec params) {
        
        if (s == null) {
            throw new NullPointerException("s is null");
        }
        if (params == null) {
            throw new NullPointerException("params is null");
        }
        this.s = s;
        this.params = params;
    }
    
    public BigInteger getS() {
        return s;
    }
    
    public ECParameterSpec getParams() {
        return params;
    }
}
