package java.awt.image;

import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.GraphicsConfiguration;
import java.awt.Image;
import java.awt.ImageCapabilities;
import java.awt.Transparency;

public abstract class VolatileImage extends Image implements Transparency {
    
    public VolatileImage() {
        
    }
    public static final int IMAGE_OK = 0;
    public static final int IMAGE_RESTORED = 1;
    public static final int IMAGE_INCOMPATIBLE = 2;
    
    public abstract BufferedImage getSnapshot();
    
    public abstract int getWidth();
    
    public abstract int getHeight();
    
    public ImageProducer getSource() {
        return getSnapshot().getSource();
    }
    
    public void flush() {
    }
    
    public Graphics getGraphics() {
        return createGraphics();
    }
    
    public abstract Graphics2D createGraphics();
    
    public abstract int validate(GraphicsConfiguration gc);
    
    public abstract boolean contentsLost();
    
    public abstract ImageCapabilities getCapabilities();
    protected int transparency = TRANSLUCENT;
    
    public int getTransparency() {
        return transparency;
    }
}
