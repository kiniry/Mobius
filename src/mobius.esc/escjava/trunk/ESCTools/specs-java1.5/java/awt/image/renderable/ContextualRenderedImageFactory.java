package java.awt.image.renderable;

import java.awt.geom.Rectangle2D;
import java.awt.image.RenderedImage;

public interface ContextualRenderedImageFactory extends RenderedImageFactory {
    
    RenderContext mapRenderContext(int i, RenderContext renderContext, ParameterBlock paramBlock, RenderableImage image);
    
    RenderedImage create(RenderContext renderContext, ParameterBlock paramBlock);
    
    Rectangle2D getBounds2D(ParameterBlock paramBlock);
    
    Object getProperty(ParameterBlock paramBlock, String name);
    
    String[] getPropertyNames();
    
    boolean isDynamic();
}
