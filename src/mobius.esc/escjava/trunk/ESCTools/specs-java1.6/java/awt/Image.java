package java.awt;

import java.awt.image.ImageProducer;
import java.awt.image.ImageObserver;
import java.awt.image.ImageFilter;
import java.awt.image.FilteredImageSource;
import java.awt.image.AreaAveragingScaleFilter;
import java.awt.image.ReplicateScaleFilter;

public abstract class Image {
    
    public Image() {
        
    }
    private static ImageCapabilities defaultImageCaps = new ImageCapabilities(false);
    protected float accelerationPriority = 0.5F;
    
    public abstract int getWidth(ImageObserver observer);
    
    public abstract int getHeight(ImageObserver observer);
    
    public abstract ImageProducer getSource();
    
    public abstract Graphics getGraphics();
    
    public abstract Object getProperty(String name, ImageObserver observer);
    public static final Object UndefinedProperty = new Object();
    
    public Image getScaledInstance(int width, int height, int hints) {
        ImageFilter filter;
        if ((hints & (SCALE_SMOOTH | SCALE_AREA_AVERAGING)) != 0) {
            filter = new AreaAveragingScaleFilter(width, height);
        } else {
            filter = new ReplicateScaleFilter(width, height);
        }
        ImageProducer prod;
        prod = new FilteredImageSource(getSource(), filter);
        return Toolkit.getDefaultToolkit().createImage(prod);
    }
    public static final int SCALE_DEFAULT = 1;
    public static final int SCALE_FAST = 2;
    public static final int SCALE_SMOOTH = 4;
    public static final int SCALE_REPLICATE = 8;
    public static final int SCALE_AREA_AVERAGING = 16;
    
    public abstract void flush();
    
    public ImageCapabilities getCapabilities(GraphicsConfiguration gc) {
        return defaultImageCaps;
    }
    
    public void setAccelerationPriority(float priority) {
        if (priority < 0 || priority > 1) {
            throw new IllegalArgumentException("Priority must be a value between 0 and 1, inclusive");
        }
        accelerationPriority = priority;
    }
    
    public float getAccelerationPriority() {
        return accelerationPriority;
    }
}
