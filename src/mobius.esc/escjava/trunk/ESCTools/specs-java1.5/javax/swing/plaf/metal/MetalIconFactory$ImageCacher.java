package javax.swing.plaf.metal;

import javax.swing.*;
import java.awt.*;
import java.util.Enumeration;
import java.util.Vector;

class MetalIconFactory$ImageCacher {
    
    MetalIconFactory$ImageCacher() {
        
    }
    Vector images = new Vector(1, 1);
    MetalIconFactory$ImageCacher$ImageGcPair currentImageGcPair;
    {
    }
    
    Image getImage(GraphicsConfiguration newGC) {
        if ((currentImageGcPair == null) || !(currentImageGcPair.hasSameConfiguration(newGC))) {
            Enumeration elements = images.elements();
            while (elements.hasMoreElements()) {
                MetalIconFactory$ImageCacher$ImageGcPair imgGcPair = (MetalIconFactory$ImageCacher$ImageGcPair)(MetalIconFactory$ImageCacher$ImageGcPair)elements.nextElement();
                if (imgGcPair.hasSameConfiguration(newGC)) {
                    currentImageGcPair = imgGcPair;
                    return imgGcPair.image;
                }
            }
            return null;
        }
        return currentImageGcPair.image;
    }
    
    void cacheImage(Image image, GraphicsConfiguration gc) {
        MetalIconFactory$ImageCacher$ImageGcPair imgGcPair = new MetalIconFactory$ImageCacher$ImageGcPair(this, image, gc);
        images.addElement(imgGcPair);
        currentImageGcPair = imgGcPair;
    }
}
