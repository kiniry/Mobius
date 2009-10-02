package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import java.awt.Component;
import java.awt.Insets;
import java.awt.Dimension;
import java.awt.Rectangle;
import java.awt.Color;
import java.awt.Graphics;

class BasicBorders$SplitPaneDividerBorder implements Border, UIResource {
    Color highlight;
    Color shadow;
    
    BasicBorders$SplitPaneDividerBorder(Color highlight, Color shadow) {
        
        this.highlight = highlight;
        this.shadow = shadow;
    }
    
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
        Component child;
        Rectangle cBounds;
        JSplitPane splitPane = ((BasicSplitPaneDivider)(BasicSplitPaneDivider)c).getBasicSplitPaneUI().getSplitPane();
        Dimension size = c.getSize();
        child = splitPane.getLeftComponent();
        g.setColor(c.getBackground());
        g.drawRect(x, y, width - 1, height - 1);
        if (splitPane.getOrientation() == JSplitPane.HORIZONTAL_SPLIT) {
            if (child != null) {
                g.setColor(highlight);
                g.drawLine(0, 0, 0, size.height);
            }
            child = splitPane.getRightComponent();
            if (child != null) {
                g.setColor(shadow);
                g.drawLine(size.width - 1, 0, size.width - 1, size.height);
            }
        } else {
            if (child != null) {
                g.setColor(highlight);
                g.drawLine(0, 0, size.width, 0);
            }
            child = splitPane.getRightComponent();
            if (child != null) {
                g.setColor(shadow);
                g.drawLine(0, size.height - 1, size.width, size.height - 1);
            }
        }
    }
    
    public Insets getBorderInsets(Component c) {
        Insets insets = new Insets(0, 0, 0, 0);
        if (c instanceof BasicSplitPaneDivider) {
            BasicSplitPaneUI bspui = ((BasicSplitPaneDivider)(BasicSplitPaneDivider)c).getBasicSplitPaneUI();
            if (bspui != null) {
                JSplitPane splitPane = bspui.getSplitPane();
                if (splitPane != null) {
                    if (splitPane.getOrientation() == JSplitPane.HORIZONTAL_SPLIT) {
                        insets.top = insets.bottom = 0;
                        insets.left = insets.right = 1;
                        return insets;
                    }
                    insets.top = insets.bottom = 1;
                    insets.left = insets.right = 0;
                    return insets;
                }
            }
        }
        insets.top = insets.bottom = insets.left = insets.right = 1;
        return insets;
    }
    
    public boolean isBorderOpaque() {
        return true;
    }
}
