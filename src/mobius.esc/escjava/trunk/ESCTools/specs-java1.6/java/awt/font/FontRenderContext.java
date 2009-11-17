package java.awt.font;

import java.awt.geom.AffineTransform;

public class FontRenderContext {
    private transient AffineTransform tx;
    private transient boolean bIsAntiAliased;
    private transient boolean bUsesFractionalMetrics;
    
    protected FontRenderContext() {
        
    }
    
    public FontRenderContext(AffineTransform tx, boolean isAntiAliased, boolean usesFractionalMetrics) {
        
        if (tx != null && !tx.isIdentity()) {
            this.tx = new AffineTransform(tx);
        }
        this.bIsAntiAliased = isAntiAliased;
        this.bUsesFractionalMetrics = usesFractionalMetrics;
    }
    
    public AffineTransform getTransform() {
        return (tx == null) ? new AffineTransform() : new AffineTransform(tx);
    }
    
    public boolean isAntiAliased() {
        return this.bIsAntiAliased;
    }
    
    public boolean usesFractionalMetrics() {
        return this.bUsesFractionalMetrics;
    }
    
    public boolean equals(Object obj) {
        try {
            return equals((FontRenderContext)(FontRenderContext)obj);
        } catch (ClassCastException e) {
            return false;
        }
    }
    
    public boolean equals(FontRenderContext rhs) {
        if (this == rhs) {
            return true;
        }
        if (rhs != null && rhs.bIsAntiAliased == bIsAntiAliased && rhs.bUsesFractionalMetrics == bUsesFractionalMetrics) {
            return tx == null ? rhs.tx == null : tx.equals(rhs.tx);
        }
        return false;
    }
    
    public int hashCode() {
        int hash = tx == null ? 0 : tx.hashCode();
        if (bIsAntiAliased) {
            hash ^= 1;
        }
        if (bUsesFractionalMetrics) {
            hash ^= 2;
        }
        return hash;
    }
}
