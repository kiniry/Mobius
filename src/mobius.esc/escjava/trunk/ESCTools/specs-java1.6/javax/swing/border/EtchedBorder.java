package javax.swing.border;

import java.awt.Graphics;
import java.awt.Insets;
import java.awt.Color;
import java.awt.Component;

public class EtchedBorder extends AbstractBorder {
    public static final int RAISED = 0;
    public static final int LOWERED = 1;
    protected int etchType;
    protected Color highlight;
    protected Color shadow;
    
    public EtchedBorder() {
        this(LOWERED);
    }
    
    public EtchedBorder(int etchType) {
        this(etchType, null, null);
    }
    
    public EtchedBorder(Color highlight, Color shadow) {
        this(LOWERED, highlight, shadow);
    }
    
    public EtchedBorder(int etchType, Color highlight, Color shadow) {
        
        this.etchType = etchType;
        this.highlight = highlight;
        this.shadow = shadow;
    }
    
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
        int w = width;
        int h = height;
        g.translate(x, y);
        g.setColor(etchType == LOWERED ? getShadowColor(c) : getHighlightColor(c));
        g.drawRect(0, 0, w - 2, h - 2);
        g.setColor(etchType == LOWERED ? getHighlightColor(c) : getShadowColor(c));
        g.drawLine(1, h - 3, 1, 1);
        g.drawLine(1, 1, w - 3, 1);
        g.drawLine(0, h - 1, w - 1, h - 1);
        g.drawLine(w - 1, h - 1, w - 1, 0);
        g.translate(-x, -y);
    }
    
    public Insets getBorderInsets(Component c) {
        return new Insets(2, 2, 2, 2);
    }
    
    public Insets getBorderInsets(Component c, Insets insets) {
        insets.left = insets.top = insets.right = insets.bottom = 2;
        return insets;
    }
    
    public boolean isBorderOpaque() {
        return true;
    }
    
    public int getEtchType() {
        return etchType;
    }
    
    public Color getHighlightColor(Component c) {
        return highlight != null ? highlight : c.getBackground().brighter();
    }
    
    public Color getHighlightColor() {
        return highlight;
    }
    
    public Color getShadowColor(Component c) {
        return shadow != null ? shadow : c.getBackground().darker();
    }
    
    public Color getShadowColor() {
        return shadow;
    }
}
