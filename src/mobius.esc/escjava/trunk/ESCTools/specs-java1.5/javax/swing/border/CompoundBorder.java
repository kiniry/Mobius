package javax.swing.border;

import java.awt.Graphics;
import java.awt.Insets;
import java.awt.Component;

public class CompoundBorder extends AbstractBorder {
    protected Border outsideBorder;
    protected Border insideBorder;
    
    public CompoundBorder() {
        
        this.outsideBorder = null;
        this.insideBorder = null;
    }
    
    public CompoundBorder(Border outsideBorder, Border insideBorder) {
        
        this.outsideBorder = outsideBorder;
        this.insideBorder = insideBorder;
    }
    
    public boolean isBorderOpaque() {
        return (outsideBorder == null || outsideBorder.isBorderOpaque()) && (insideBorder == null || insideBorder.isBorderOpaque());
    }
    
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
        Insets nextInsets;
        int px;
        int py;
        int pw;
        int ph;
        px = x;
        py = y;
        pw = width;
        ph = height;
        if (outsideBorder != null) {
            outsideBorder.paintBorder(c, g, px, py, pw, ph);
            nextInsets = outsideBorder.getBorderInsets(c);
            px += nextInsets.left;
            py += nextInsets.top;
            pw = pw - nextInsets.right - nextInsets.left;
            ph = ph - nextInsets.bottom - nextInsets.top;
        }
        if (insideBorder != null) insideBorder.paintBorder(c, g, px, py, pw, ph);
    }
    
    public Insets getBorderInsets(Component c, Insets insets) {
        Insets nextInsets;
        insets.top = insets.left = insets.right = insets.bottom = 0;
        if (outsideBorder != null) {
            nextInsets = outsideBorder.getBorderInsets(c);
            insets.top += nextInsets.top;
            insets.left += nextInsets.left;
            insets.right += nextInsets.right;
            insets.bottom += nextInsets.bottom;
        }
        if (insideBorder != null) {
            nextInsets = insideBorder.getBorderInsets(c);
            insets.top += nextInsets.top;
            insets.left += nextInsets.left;
            insets.right += nextInsets.right;
            insets.bottom += nextInsets.bottom;
        }
        return insets;
    }
    
    public Insets getBorderInsets(Component c) {
        return getBorderInsets(c, new Insets(0, 0, 0, 0));
    }
    
    public Border getOutsideBorder() {
        return outsideBorder;
    }
    
    public Border getInsideBorder() {
        return insideBorder;
    }
}
