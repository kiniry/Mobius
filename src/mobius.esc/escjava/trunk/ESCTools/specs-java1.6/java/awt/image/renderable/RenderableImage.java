package java.awt.image.renderable;

import java.util.Vector;
import java.awt.RenderingHints;
import java.awt.image.*;

public interface RenderableImage {
    static final String HINTS_OBSERVED = "HINTS_OBSERVED";
    
    Vector getSources();
    
    Object getProperty(String name);
    
    String[] getPropertyNames();
    
    boolean isDynamic();
    
    float getWidth();
    
    float getHeight();
    
    float getMinX();
    
    float getMinY();
    
    RenderedImage createScaledRendering(int w, int h, RenderingHints hints);
    
    RenderedImage createDefaultRendering();
    
    RenderedImage createRendering(RenderContext renderContext);
}
