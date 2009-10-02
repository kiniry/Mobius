package java.awt;

import java.awt.geom.Rectangle2D;
import java.awt.geom.AffineTransform;
import java.awt.image.BufferedImage;
import java.awt.image.ColorModel;

public class TexturePaint implements Paint {
    BufferedImage bufImg;
    double tx;
    double ty;
    double sx;
    double sy;
    
    public TexturePaint(BufferedImage txtr, Rectangle2D anchor) {
        
        this.bufImg = txtr;
        this.tx = anchor.getX();
        this.ty = anchor.getY();
        this.sx = anchor.getWidth() / bufImg.getWidth();
        this.sy = anchor.getHeight() / bufImg.getHeight();
    }
    
    public BufferedImage getImage() {
        return bufImg;
    }
    
    public Rectangle2D getAnchorRect() {
        return new Rectangle2D$Double(tx, ty, sx * bufImg.getWidth(), sy * bufImg.getHeight());
    }
    
    public PaintContext createContext(ColorModel cm, Rectangle deviceBounds, Rectangle2D userBounds, AffineTransform xform, RenderingHints hints) {
        if (xform == null) {
            xform = new AffineTransform();
        } else {
            xform = (AffineTransform)(AffineTransform)xform.clone();
        }
        xform.translate(tx, ty);
        xform.scale(sx, sy);
        return TexturePaintContext.getContext(bufImg, xform, hints, deviceBounds);
    }
    
    public int getTransparency() {
        return (bufImg.getColorModel()).getTransparency();
    }
}
