package java.awt;

import java.awt.RenderingHints.Key;
import java.awt.geom.AffineTransform;
import java.awt.image.ImageObserver;
import java.awt.image.BufferedImageOp;
import java.awt.image.BufferedImage;
import java.awt.image.RenderedImage;
import java.awt.image.renderable.RenderableImage;
import java.awt.font.GlyphVector;
import java.awt.font.FontRenderContext;
import java.text.AttributedCharacterIterator;
import java.util.Map;

public abstract class Graphics2D extends Graphics {
    
    protected Graphics2D() {
        
    }
    
    public void draw3DRect(int x, int y, int width, int height, boolean raised) {
        Paint p = getPaint();
        Color c = getColor();
        Color brighter = c.brighter();
        Color darker = c.darker();
        setColor(raised ? brighter : darker);
        fillRect(x, y, 1, height + 1);
        fillRect(x + 1, y, width - 1, 1);
        setColor(raised ? darker : brighter);
        fillRect(x + 1, y + height, width, 1);
        fillRect(x + width, y, 1, height);
        setPaint(p);
    }
    
    public void fill3DRect(int x, int y, int width, int height, boolean raised) {
        Paint p = getPaint();
        Color c = getColor();
        Color brighter = c.brighter();
        Color darker = c.darker();
        if (!raised) {
            setColor(darker);
        } else if (p != c) {
            setColor(c);
        }
        fillRect(x + 1, y + 1, width - 2, height - 2);
        setColor(raised ? brighter : darker);
        fillRect(x, y, 1, height);
        fillRect(x + 1, y, width - 2, 1);
        setColor(raised ? darker : brighter);
        fillRect(x + 1, y + height - 1, width - 1, 1);
        fillRect(x + width - 1, y, 1, height - 1);
        setPaint(p);
    }
    
    public abstract void draw(Shape s);
    
    public abstract boolean drawImage(Image img, AffineTransform xform, ImageObserver obs);
    
    public abstract void drawImage(BufferedImage img, BufferedImageOp op, int x, int y);
    
    public abstract void drawRenderedImage(RenderedImage img, AffineTransform xform);
    
    public abstract void drawRenderableImage(RenderableImage img, AffineTransform xform);
    
    public abstract void drawString(String str, int x, int y);
    
    public abstract void drawString(String s, float x, float y);
    
    public abstract void drawString(AttributedCharacterIterator iterator, int x, int y);
    
    public abstract void drawString(AttributedCharacterIterator iterator, float x, float y);
    
    public abstract void drawGlyphVector(GlyphVector g, float x, float y);
    
    public abstract void fill(Shape s);
    
    public abstract boolean hit(Rectangle rect, Shape s, boolean onStroke);
    
    public abstract GraphicsConfiguration getDeviceConfiguration();
    
    public abstract void setComposite(Composite comp);
    
    public abstract void setPaint(Paint paint);
    
    public abstract void setStroke(Stroke s);
    
    public abstract void setRenderingHint(RenderingHints$Key hintKey, Object hintValue);
    
    public abstract Object getRenderingHint(RenderingHints$Key hintKey);
    
    public abstract void setRenderingHints(Map hints);
    
    public abstract void addRenderingHints(Map hints);
    
    public abstract RenderingHints getRenderingHints();
    
    public abstract void translate(int x, int y);
    
    public abstract void translate(double tx, double ty);
    
    public abstract void rotate(double theta);
    
    public abstract void rotate(double theta, double x, double y);
    
    public abstract void scale(double sx, double sy);
    
    public abstract void shear(double shx, double shy);
    
    public abstract void transform(AffineTransform Tx);
    
    public abstract void setTransform(AffineTransform Tx);
    
    public abstract AffineTransform getTransform();
    
    public abstract Paint getPaint();
    
    public abstract Composite getComposite();
    
    public abstract void setBackground(Color color);
    
    public abstract Color getBackground();
    
    public abstract Stroke getStroke();
    
    public abstract void clip(Shape s);
    
    public abstract FontRenderContext getFontRenderContext();
}
