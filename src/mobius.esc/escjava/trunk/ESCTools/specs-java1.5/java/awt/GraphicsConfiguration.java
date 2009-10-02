package java.awt;

import java.awt.geom.AffineTransform;
import java.awt.image.BufferedImage;
import java.awt.image.ColorModel;
import java.awt.image.VolatileImage;

public abstract class GraphicsConfiguration {
    private static BufferCapabilities defaultBufferCaps;
    private static ImageCapabilities defaultImageCaps;
    
    protected GraphicsConfiguration() {
        
    }
    
    public abstract GraphicsDevice getDevice();
    
    public abstract BufferedImage createCompatibleImage(int width, int height);
    
    public abstract VolatileImage createCompatibleVolatileImage(int width, int height);
    
    public abstract VolatileImage createCompatibleVolatileImage(int width, int height, int transparency);
    
    public VolatileImage createCompatibleVolatileImage(int width, int height, ImageCapabilities caps) throws AWTException {
        return createCompatibleVolatileImage(width, height);
    }
    
    public VolatileImage createCompatibleVolatileImage(int width, int height, ImageCapabilities caps, int transparency) throws AWTException {
        return createCompatibleVolatileImage(width, height, transparency);
    }
    
    public abstract BufferedImage createCompatibleImage(int width, int height, int transparency);
    
    public abstract ColorModel getColorModel();
    
    public abstract ColorModel getColorModel(int transparency);
    
    public abstract AffineTransform getDefaultTransform();
    
    public abstract AffineTransform getNormalizingTransform();
    
    public abstract Rectangle getBounds();
    {
    }
    
    public BufferCapabilities getBufferCapabilities() {
        if (defaultBufferCaps == null) {
            defaultBufferCaps = new GraphicsConfiguration$DefaultBufferCapabilities(getImageCapabilities());
        }
        return defaultBufferCaps;
    }
    
    public ImageCapabilities getImageCapabilities() {
        if (defaultImageCaps == null) {
            defaultImageCaps = new ImageCapabilities(false);
        }
        return defaultImageCaps;
    }
}
