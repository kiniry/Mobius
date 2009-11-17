package java.awt.font;

import java.awt.Image;
import java.awt.Graphics2D;
import java.awt.geom.Rectangle2D;

public final class ImageGraphicAttribute extends GraphicAttribute {
    private Image fImage;
    private float fImageWidth;
    private float fImageHeight;
    private float fOriginX;
    private float fOriginY;
    
    public ImageGraphicAttribute(Image image, int alignment) {
        this(image, alignment, 0, 0);
    }
    
    public ImageGraphicAttribute(Image image, int alignment, float originX, float originY) {
        super(alignment);
        fImage = image;
        fImageWidth = image.getWidth(null);
        fImageHeight = image.getHeight(null);
        fOriginX = originX;
        fOriginY = originY;
    }
    
    public float getAscent() {
        return Math.max(0, fOriginY);
    }
    
    public float getDescent() {
        return Math.max(0, fImageHeight - fOriginY);
    }
    
    public float getAdvance() {
        return Math.max(0, fImageWidth - fOriginX);
    }
    
    public Rectangle2D getBounds() {
        return new Rectangle2D$Float(-fOriginX, -fOriginY, fImageWidth, fImageHeight);
    }
    
    public void draw(Graphics2D graphics, float x, float y) {
        graphics.drawImage(fImage, (int)(x - fOriginX), (int)(y - fOriginY), null);
    }
    
    public int hashCode() {
        return fImage.hashCode();
    }
    
    public boolean equals(Object rhs) {
        try {
            return equals((ImageGraphicAttribute)(ImageGraphicAttribute)rhs);
        } catch (ClassCastException e) {
            return false;
        }
    }
    
    public boolean equals(ImageGraphicAttribute rhs) {
        if (rhs == null) {
            return false;
        }
        if (this == rhs) {
            return true;
        }
        if (fOriginX != rhs.fOriginX || fOriginY != rhs.fOriginY) {
            return false;
        }
        if (getAlignment() != rhs.getAlignment()) {
            return false;
        }
        if (!fImage.equals(rhs.fImage)) {
            return false;
        }
        return true;
    }
}
