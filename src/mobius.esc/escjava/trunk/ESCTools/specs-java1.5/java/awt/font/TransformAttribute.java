package java.awt.font;

import java.awt.geom.AffineTransform;
import java.io.Serializable;

public final class TransformAttribute implements Serializable {
    private AffineTransform transform;
    
    public TransformAttribute(AffineTransform transform) {
        
        if (transform == null) {
            throw new IllegalArgumentException("transform may not be null");
        }
        if (!transform.isIdentity()) {
            this.transform = new AffineTransform(transform);
        }
    }
    
    public AffineTransform getTransform() {
        AffineTransform at = transform;
        return (at == null) ? new AffineTransform() : new AffineTransform(at);
    }
    
    public boolean isIdentity() {
        return (transform == null);
    }
    
    private void writeObject(java.io.ObjectOutputStream s) throws java.lang.ClassNotFoundException, java.io.IOException {
        if (this.transform == null) {
            this.transform = new AffineTransform();
        }
        s.defaultWriteObject();
    }
    static final long serialVersionUID = 3356247357827709530L;
}
