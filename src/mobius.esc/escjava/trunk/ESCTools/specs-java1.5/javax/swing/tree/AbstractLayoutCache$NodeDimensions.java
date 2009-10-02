package javax.swing.tree;

import java.awt.Rectangle;

public abstract class AbstractLayoutCache$NodeDimensions {
    
    public AbstractLayoutCache$NodeDimensions() {
        
    }
    
    public abstract Rectangle getNodeDimensions(Object value, int row, int depth, boolean expanded, Rectangle bounds);
}
