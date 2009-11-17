package java.awt.image.renderable;

import java.awt.image.RenderedImage;
import java.awt.RenderingHints;

public interface RenderedImageFactory {
    
    RenderedImage create(ParameterBlock paramBlock, RenderingHints hints);
}
