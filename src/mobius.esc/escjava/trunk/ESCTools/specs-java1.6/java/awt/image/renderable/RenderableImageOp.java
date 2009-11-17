package java.awt.image.renderable;

import java.awt.geom.AffineTransform;
import java.awt.geom.Rectangle2D;
import java.awt.image.RenderedImage;
import java.awt.RenderingHints;
import java.util.Vector;

public class RenderableImageOp implements RenderableImage {
    ParameterBlock paramBlock;
    ContextualRenderedImageFactory myCRIF;
    Rectangle2D boundingBox;
    
    public RenderableImageOp(ContextualRenderedImageFactory CRIF, ParameterBlock paramBlock) {
        
        this.myCRIF = CRIF;
        this.paramBlock = (ParameterBlock)(ParameterBlock)paramBlock.clone();
    }
    
    public Vector getSources() {
        return getRenderableSources();
    }
    
    private Vector getRenderableSources() {
        Vector sources = null;
        if (paramBlock.getNumSources() > 0) {
            sources = new Vector();
            int i = 0;
            while (i < paramBlock.getNumSources()) {
                Object o = paramBlock.getSource(i);
                if (o instanceof RenderableImage) {
                    sources.add((RenderableImage)(RenderableImage)o);
                    i++;
                } else {
                    break;
                }
            }
        }
        return sources;
    }
    
    public Object getProperty(String name) {
        return myCRIF.getProperty(paramBlock, name);
    }
    
    public String[] getPropertyNames() {
        return myCRIF.getPropertyNames();
    }
    
    public boolean isDynamic() {
        return myCRIF.isDynamic();
    }
    
    public float getWidth() {
        if (boundingBox == null) {
            boundingBox = myCRIF.getBounds2D(paramBlock);
        }
        return (float)boundingBox.getWidth();
    }
    
    public float getHeight() {
        if (boundingBox == null) {
            boundingBox = myCRIF.getBounds2D(paramBlock);
        }
        return (float)boundingBox.getHeight();
    }
    
    public float getMinX() {
        if (boundingBox == null) {
            boundingBox = myCRIF.getBounds2D(paramBlock);
        }
        return (float)boundingBox.getMinX();
    }
    
    public float getMinY() {
        if (boundingBox == null) {
            boundingBox = myCRIF.getBounds2D(paramBlock);
        }
        return (float)boundingBox.getMinY();
    }
    
    public ParameterBlock setParameterBlock(ParameterBlock paramBlock) {
        ParameterBlock oldParamBlock = this.paramBlock;
        this.paramBlock = (ParameterBlock)(ParameterBlock)paramBlock.clone();
        return oldParamBlock;
    }
    
    public ParameterBlock getParameterBlock() {
        return paramBlock;
    }
    
    public RenderedImage createScaledRendering(int w, int h, RenderingHints hints) {
        double sx = (double)w / getWidth();
        double sy = (double)h / getHeight();
        if (Math.abs(sx / sy - 1.0) < 0.01) {
            sx = sy;
        }
        AffineTransform usr2dev = AffineTransform.getScaleInstance(sx, sy);
        RenderContext newRC = new RenderContext(usr2dev, hints);
        return createRendering(newRC);
    }
    
    public RenderedImage createDefaultRendering() {
        AffineTransform usr2dev = new AffineTransform();
        RenderContext newRC = new RenderContext(usr2dev);
        return createRendering(newRC);
    }
    
    public RenderedImage createRendering(RenderContext renderContext) {
        RenderedImage image = null;
        RenderContext rcOut = null;
        ParameterBlock renderedParamBlock = (ParameterBlock)(ParameterBlock)paramBlock.clone();
        Vector sources = getRenderableSources();
        try {
            if (sources != null) {
                Vector renderedSources = new Vector();
                for (int i = 0; i < sources.size(); i++) {
                    rcOut = myCRIF.mapRenderContext(i, renderContext, paramBlock, this);
                    RenderedImage rdrdImage = ((RenderableImage)(RenderableImage)sources.elementAt(i)).createRendering(rcOut);
                    if (rdrdImage == null) {
                        return null;
                    }
                    renderedSources.addElement(rdrdImage);
                }
                if (renderedSources.size() > 0) {
                    renderedParamBlock.setSources(renderedSources);
                }
            }
            return myCRIF.create(renderContext, renderedParamBlock);
        } catch (ArrayIndexOutOfBoundsException e) {
            return null;
        }
    }
}
