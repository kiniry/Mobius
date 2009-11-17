package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import java.awt.Component;
import java.awt.Insets;
import java.awt.Rectangle;
import java.awt.Color;
import java.awt.Graphics;

public class BasicBorders$SplitPaneBorder implements Border, UIResource {
    protected Color highlight;
    protected Color shadow;
    
    public BasicBorders$SplitPaneBorder(Color highlight, Color shadow) {
        
        this.highlight = highlight;
        this.shadow = shadow;
    }
    
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
        Component child;
        Rectangle cBounds;
        JSplitPane splitPane = (JSplitPane)(JSplitPane)c;
        child = splitPane.getLeftComponent();
        g.setColor(c.getBackground());
        g.drawRect(x, y, width - 1, height - 1);
        if (splitPane.getOrientation() == JSplitPane.HORIZONTAL_SPLIT) {
            if (child != null) {
                cBounds = child.getBounds();
                g.setColor(shadow);
                g.drawLine(0, 0, cBounds.width + 1, 0);
                g.drawLine(0, 1, 0, cBounds.height + 2);
                g.setColor(highlight);
                g.drawLine(1, cBounds.height + 1, cBounds.width + 1, cBounds.height + 1);
            }
            child = splitPane.getRightComponent();
            if (child != null) {
                cBounds = child.getBounds();
                int maxX = cBounds.x + cBounds.width;
                int maxY = cBounds.y + cBounds.height;
                g.setColor(shadow);
                g.drawLine(cBounds.x - 1, 0, maxX, 0);
                g.drawLine(cBounds.x - 1, maxY, cBounds.x, maxY);
                g.setColor(highlight);
                g.drawLine(cBounds.x, maxY, maxX, maxY);
                g.drawLine(maxX, 0, maxX, maxY + 1);
            }
        } else {
            if (child != null) {
                cBounds = child.getBounds();
                g.setColor(shadow);
                g.drawLine(0, 0, cBounds.width + 1, 0);
                g.drawLine(0, 1, 0, cBounds.height);
                g.setColor(highlight);
                g.drawLine(1 + cBounds.width, 0, 1 + cBounds.width, cBounds.height + 1);
                g.drawLine(0, cBounds.height + 1, 0, cBounds.height + 1);
            }
            child = splitPane.getRightComponent();
            if (child != null) {
                cBounds = child.getBounds();
                int maxX = cBounds.x + cBounds.width;
                int maxY = cBounds.y + cBounds.height;
                g.setColor(shadow);
                g.drawLine(0, cBounds.y - 1, 0, maxY);
                g.drawLine(maxX, cBounds.y - 1, maxX, cBounds.y - 1);
                g.setColor(highlight);
                g.drawLine(0, maxY, cBounds.width + 1, maxY);
                g.drawLine(maxX, cBounds.y, maxX, maxY);
            }
        }
    }
    
    public Insets getBorderInsets(Component c) {
        return new Insets(1, 1, 1, 1);
    }
    
    public boolean isBorderOpaque() {
        return true;
    }
}
