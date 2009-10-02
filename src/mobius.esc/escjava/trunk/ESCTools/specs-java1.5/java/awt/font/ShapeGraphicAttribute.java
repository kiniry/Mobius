package java.awt.font;

import java.awt.Shape;
import java.awt.Graphics2D;
import java.awt.geom.Rectangle2D;

public final class ShapeGraphicAttribute extends GraphicAttribute {
    private Shape fShape;
    private boolean fStroke;
    public static final boolean STROKE = true;
    public static final boolean FILL = false;
    private Rectangle2D fShapeBounds;
    
    public ShapeGraphicAttribute(Shape shape, int alignment, boolean stroke) {
        super(alignment);
        fShape = shape;
        fStroke = stroke;
        fShapeBounds = fShape.getBounds2D();
    }
    
    public float getAscent() {
        return (float)Math.max(0, -fShapeBounds.getMinY());
    }
    
    public float getDescent() {
        return (float)Math.max(0, fShapeBounds.getMaxY());
    }
    
    public float getAdvance() {
        return (float)Math.max(0, fShapeBounds.getMaxX());
    }
    
    public void draw(Graphics2D graphics, float x, float y) {
        graphics.translate((int)x, (int)y);
        try {
            if (fStroke == STROKE) {
                graphics.draw(fShape);
            } else {
                graphics.fill(fShape);
            }
        } finally {
            graphics.translate(-(int)x, -(int)y);
        }
    }
    
    public Rectangle2D getBounds() {
        Rectangle2D$Float bounds = new Rectangle2D$Float();
        bounds.setRect(fShapeBounds);
        if (fStroke == STROKE) {
            ++bounds.width;
            ++bounds.height;
        }
        return bounds;
    }
    
    public int hashCode() {
        return fShape.hashCode();
    }
    
    public boolean equals(Object rhs) {
        try {
            return equals((ShapeGraphicAttribute)(ShapeGraphicAttribute)rhs);
        } catch (ClassCastException e) {
            return false;
        }
    }
    
    public boolean equals(ShapeGraphicAttribute rhs) {
        if (rhs == null) {
            return false;
        }
        if (this == rhs) {
            return true;
        }
        if (fStroke != rhs.fStroke) {
            return false;
        }
        if (getAlignment() != rhs.getAlignment()) {
            return false;
        }
        if (!fShape.equals(rhs.fShape)) {
            return false;
        }
        return true;
    }
}
