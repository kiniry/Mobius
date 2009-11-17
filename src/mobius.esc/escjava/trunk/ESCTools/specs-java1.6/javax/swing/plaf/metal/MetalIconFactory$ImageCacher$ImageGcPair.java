package javax.swing.plaf.metal;

import javax.swing.*;
import java.awt.*;

class MetalIconFactory$ImageCacher$ImageGcPair {
    /*synthetic*/ final MetalIconFactory$ImageCacher this$0;
    Image image;
    GraphicsConfiguration gc;
    
    MetalIconFactory$ImageCacher$ImageGcPair(/*synthetic*/ final MetalIconFactory$ImageCacher this$0, Image image, GraphicsConfiguration gc) {
        this.this$0 = this$0;
        
        this.image = image;
        this.gc = gc;
    }
    
    boolean hasSameConfiguration(GraphicsConfiguration newGC) {
        if (((newGC != null) && (newGC.equals(gc))) || ((newGC == null) && (gc == null))) {
            return true;
        }
        return false;
    }
}
