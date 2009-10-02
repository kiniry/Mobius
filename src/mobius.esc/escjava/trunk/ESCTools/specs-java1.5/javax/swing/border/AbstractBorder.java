package javax.swing.border;

import java.awt.Graphics;
import java.awt.Insets;
import java.awt.Rectangle;
import java.awt.Component;
import java.io.Serializable;

public abstract class AbstractBorder implements Border, Serializable {
    
    public AbstractBorder() {
        
    }
    
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
    }
    
    public Insets getBorderInsets(Component c) {
        return new Insets(0, 0, 0, 0);
    }
    
    public Insets getBorderInsets(Component c, Insets insets) {
        insets.left = insets.top = insets.right = insets.bottom = 0;
        return insets;
    }
    
    public boolean isBorderOpaque() {
        return false;
    }
    
    public Rectangle getInteriorRectangle(Component c, int x, int y, int width, int height) {
        return getInteriorRectangle(c, this, x, y, width, height);
    }
    
    public static Rectangle getInteriorRectangle(Component c, Border b, int x, int y, int width, int height) {
        Insets insets;
        if (b != null) insets = b.getBorderInsets(c); else insets = new Insets(0, 0, 0, 0);
        return new Rectangle(x + insets.left, y + insets.top, width - insets.right - insets.left, height - insets.top - insets.bottom);
    }
    
    static boolean isLeftToRight(Component c) {
        return c.getComponentOrientation().isLeftToRight();
    }
}
