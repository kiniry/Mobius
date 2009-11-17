package javax.swing.border;

import java.awt.Graphics;
import java.awt.Insets;
import java.awt.Color;
import java.awt.Component;

public class BevelBorder extends AbstractBorder {
    public static final int RAISED = 0;
    public static final int LOWERED = 1;
    protected int bevelType;
    protected Color highlightOuter;
    protected Color highlightInner;
    protected Color shadowInner;
    protected Color shadowOuter;
    
    public BevelBorder(int bevelType) {
        
        this.bevelType = bevelType;
    }
    
    public BevelBorder(int bevelType, Color highlight, Color shadow) {
        this(bevelType, highlight.brighter(), highlight, shadow, shadow.brighter());
    }
    
    public BevelBorder(int bevelType, Color highlightOuterColor, Color highlightInnerColor, Color shadowOuterColor, Color shadowInnerColor) {
        this(bevelType);
        this.highlightOuter = highlightOuterColor;
        this.highlightInner = highlightInnerColor;
        this.shadowOuter = shadowOuterColor;
        this.shadowInner = shadowInnerColor;
    }
    
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
        if (bevelType == RAISED) {
            paintRaisedBevel(c, g, x, y, width, height);
        } else if (bevelType == LOWERED) {
            paintLoweredBevel(c, g, x, y, width, height);
        }
    }
    
    public Insets getBorderInsets(Component c) {
        return new Insets(2, 2, 2, 2);
    }
    
    public Insets getBorderInsets(Component c, Insets insets) {
        insets.left = insets.top = insets.right = insets.bottom = 2;
        return insets;
    }
    
    public Color getHighlightOuterColor(Component c) {
        Color highlight = getHighlightOuterColor();
        return highlight != null ? highlight : c.getBackground().brighter().brighter();
    }
    
    public Color getHighlightInnerColor(Component c) {
        Color highlight = getHighlightInnerColor();
        return highlight != null ? highlight : c.getBackground().brighter();
    }
    
    public Color getShadowInnerColor(Component c) {
        Color shadow = getShadowInnerColor();
        return shadow != null ? shadow : c.getBackground().darker();
    }
    
    public Color getShadowOuterColor(Component c) {
        Color shadow = getShadowOuterColor();
        return shadow != null ? shadow : c.getBackground().darker().darker();
    }
    
    public Color getHighlightOuterColor() {
        return highlightOuter;
    }
    
    public Color getHighlightInnerColor() {
        return highlightInner;
    }
    
    public Color getShadowInnerColor() {
        return shadowInner;
    }
    
    public Color getShadowOuterColor() {
        return shadowOuter;
    }
    
    public int getBevelType() {
        return bevelType;
    }
    
    public boolean isBorderOpaque() {
        return true;
    }
    
    protected void paintRaisedBevel(Component c, Graphics g, int x, int y, int width, int height) {
        Color oldColor = g.getColor();
        int h = height;
        int w = width;
        g.translate(x, y);
        g.setColor(getHighlightOuterColor(c));
        g.drawLine(0, 0, 0, h - 2);
        g.drawLine(1, 0, w - 2, 0);
        g.setColor(getHighlightInnerColor(c));
        g.drawLine(1, 1, 1, h - 3);
        g.drawLine(2, 1, w - 3, 1);
        g.setColor(getShadowOuterColor(c));
        g.drawLine(0, h - 1, w - 1, h - 1);
        g.drawLine(w - 1, 0, w - 1, h - 2);
        g.setColor(getShadowInnerColor(c));
        g.drawLine(1, h - 2, w - 2, h - 2);
        g.drawLine(w - 2, 1, w - 2, h - 3);
        g.translate(-x, -y);
        g.setColor(oldColor);
    }
    
    protected void paintLoweredBevel(Component c, Graphics g, int x, int y, int width, int height) {
        Color oldColor = g.getColor();
        int h = height;
        int w = width;
        g.translate(x, y);
        g.setColor(getShadowInnerColor(c));
        g.drawLine(0, 0, 0, h - 1);
        g.drawLine(1, 0, w - 1, 0);
        g.setColor(getShadowOuterColor(c));
        g.drawLine(1, 1, 1, h - 2);
        g.drawLine(2, 1, w - 2, 1);
        g.setColor(getHighlightOuterColor(c));
        g.drawLine(1, h - 1, w - 1, h - 1);
        g.drawLine(w - 1, 1, w - 1, h - 2);
        g.setColor(getHighlightInnerColor(c));
        g.drawLine(2, h - 2, w - 2, h - 2);
        g.drawLine(w - 2, 2, w - 2, h - 3);
        g.translate(-x, -y);
        g.setColor(oldColor);
    }
}
