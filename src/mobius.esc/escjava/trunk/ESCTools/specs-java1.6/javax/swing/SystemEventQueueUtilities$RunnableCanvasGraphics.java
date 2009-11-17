package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import java.util.*;

class SystemEventQueueUtilities$RunnableCanvasGraphics extends Graphics {
    
    /*synthetic*/ SystemEventQueueUtilities$RunnableCanvasGraphics(javax.swing.SystemEventQueueUtilities$1 x0) {
        this();
    }
    
    private SystemEventQueueUtilities$RunnableCanvasGraphics() {
        
    }
    
    public Graphics create() {
        return this;
    }
    
    public Rectangle getClipBounds() {
        return new Rectangle(0, 0, Short.MAX_VALUE, Short.MAX_VALUE);
    }
    
    public Shape getClip() {
        return (Shape)(getClipBounds());
    }
    
    public void dispose() {
    }
    
    public void translate(int x, int y) {
    }
    
    public Color getColor() {
        return Color.black;
    }
    
    public void setColor(Color c) {
    }
    
    public void setPaintMode() {
    }
    
    public void setXORMode(Color c) {
    }
    
    public Font getFont() {
        return null;
    }
    
    public void setFont(Font font) {
    }
    
    public FontMetrics getFontMetrics(Font f) {
        return null;
    }
    
    public void clipRect(int x, int y, int width, int height) {
    }
    
    public void setClip(int x, int y, int width, int height) {
    }
    
    public void setClip(Shape clip) {
    }
    
    public void copyArea(int x, int y, int w, int h, int dx, int dy) {
    }
    
    public void drawLine(int x1, int y1, int x2, int y2) {
    }
    
    public void fillRect(int x, int y, int width, int height) {
    }
    
    public void clearRect(int x, int y, int width, int height) {
    }
    
    public void drawRoundRect(int x, int y, int w, int h, int aw, int ah) {
    }
    
    public void fillRoundRect(int x, int y, int w, int h, int aw, int ah) {
    }
    
    public void drawOval(int x, int y, int w, int h) {
    }
    
    public void fillOval(int x, int y, int w, int h) {
    }
    
    public void drawArc(int x, int y, int w, int h, int sa, int aa) {
    }
    
    public void fillArc(int x, int y, int w, int h, int sa, int aa) {
    }
    
    public void drawPolyline(int[] xPoints, int[] yPoints, int nPoints) {
    }
    
    public void drawPolygon(int[] xPoints, int[] yPoints, int nPoints) {
    }
    
    public void fillPolygon(int[] xPoints, int[] yPoints, int nPoints) {
    }
    
    public void drawString(String str, int x, int y) {
    }
    
    public void drawString(java.text.AttributedCharacterIterator iterator, int x, int y) {
    }
    
    public boolean drawImage(Image i, int x, int y, ImageObserver o) {
        return false;
    }
    
    public boolean drawImage(Image i, int x, int y, int w, int h, ImageObserver o) {
        return false;
    }
    
    public boolean drawImage(Image i, int x, int y, Color bgcolor, ImageObserver o) {
        return false;
    }
    
    public boolean drawImage(Image i, int x, int y, int w, int h, Color c, ImageObserver o) {
        return false;
    }
    
    public boolean drawImage(Image i, int dx1, int dy1, int dx2, int dy2, int sx1, int sy1, int sx2, int sy2, ImageObserver o) {
        return false;
    }
    
    public boolean drawImage(Image i, int dx1, int dy1, int dx2, int dy2, int sx1, int sy1, int sx2, int sy2, Color c, ImageObserver o) {
        return false;
    }
}
