package java.security.cert;

public abstract class CRL {
    private String type;
    
    protected CRL(String type) {
        
        this.type = type;
    }
    
    public final String getType() {
        return this.type;
    }
    
    public abstract String toString();
    
    public abstract boolean isRevoked(Certificate cert);
}
