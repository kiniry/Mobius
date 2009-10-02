package javax.swing.border;

import java.awt.Graphics;
import java.awt.Insets;
import java.awt.Color;
import java.awt.Component;

public class LineBorder extends AbstractBorder {
    private static Border blackLine;
    private static Border grayLine;
    protected int thickness;
    protected Color lineColor;
    protected boolean roundedCorners;
    
    public static Border createBlackLineBorder() {
        if (blackLine == null) {
            blackLine = new LineBorder(Color.black, 1);
        }
        return blackLine;
    }
    
    public static Border createGrayLineBorder() {
        if (grayLine == null) {
            grayLine = new LineBorder(Color.gray, 1);
        }
        return grayLine;
    }
    
    public LineBorder(Color color) {
        this(color, 1, false);
    }
    
    public LineBorder(Color color, int thickness) {
        this(color, thickness, false);
    }
    
    public LineBorder(Color color, int thickness, boolean roundedCorners) {
        
        lineColor = color;
        this.thickness = thickness;
        this.roundedCorners = roundedCorners;
    }
    
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
        Color oldColor = g.getColor();
        int i;
        g.setColor(lineColor);
        for (i = 0; i < thickness; i++) {
            if (!roundedCorners) g.drawRect(x + i, y + i, width - i - i - 1, height - i - i - 1); else g.drawRoundRect(x + i, y + i, width - i - i - 1, height - i - i - 1, thickness, thickness);
        }
        g.setColor(oldColor);
    }
    
    public Insets getBorderInsets(Component c) {
        return new Insets(thickness, thickness, thickness, thickness);
    }
    
    public Insets getBorderInsets(Component c, Insets insets) {
        insets.left = insets.top = insets.right = insets.bottom = thickness;
        return insets;
    }
    
    public Color getLineColor() {
        return lineColor;
    }
    
    public int getThickness() {
        return thickness;
    }
    
    public boolean getRoundedCorners() {
        return roundedCorners;
    }
    
    public boolean isBorderOpaque() {
        return !roundedCorners;
    }
}
