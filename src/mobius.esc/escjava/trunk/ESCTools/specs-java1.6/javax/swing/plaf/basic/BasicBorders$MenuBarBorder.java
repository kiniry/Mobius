package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import java.awt.Component;
import java.awt.Insets;
import java.awt.Color;
import java.awt.Graphics;

public class BasicBorders$MenuBarBorder extends AbstractBorder implements UIResource {
    private Color shadow;
    private Color highlight;
    
    public BasicBorders$MenuBarBorder(Color shadow, Color highlight) {
        
        this.shadow = shadow;
        this.highlight = highlight;
    }
    
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
        Color oldColor = g.getColor();
        g.translate(x, y);
        g.setColor(shadow);
        g.drawLine(0, height - 2, width, height - 2);
        g.setColor(highlight);
        g.drawLine(0, height - 1, width, height - 1);
        g.translate(-x, -y);
        g.setColor(oldColor);
    }
    
    public Insets getBorderInsets(Component c) {
        return getBorderInsets(c, new Insets(0, 0, 0, 0));
    }
    
    public Insets getBorderInsets(Component c, Insets insets) {
        insets.top = 0;
        insets.left = 0;
        insets.bottom = 2;
        insets.right = 0;
        return insets;
    }
}
