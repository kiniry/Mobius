package javax.swing.plaf.metal;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;

class MetalIconFactory$InternalFrameDefaultMenuIcon implements Icon, UIResource, Serializable {
    
    /*synthetic*/ MetalIconFactory$InternalFrameDefaultMenuIcon(javax.swing.plaf.metal.MetalIconFactory$1 x0) {
        this();
    }
    
    private MetalIconFactory$InternalFrameDefaultMenuIcon() {
        
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        Color windowBodyColor = MetalLookAndFeel.getWindowBackground();
        Color titleColor = MetalLookAndFeel.getPrimaryControl();
        Color edgeColor = MetalLookAndFeel.getPrimaryControlDarkShadow();
        g.translate(x, y);
        g.setColor(titleColor);
        g.fillRect(0, 0, 16, 16);
        g.setColor(windowBodyColor);
        g.fillRect(2, 6, 13, 9);
        g.drawLine(2, 2, 2, 2);
        g.drawLine(5, 2, 5, 2);
        g.drawLine(8, 2, 8, 2);
        g.drawLine(11, 2, 11, 2);
        g.setColor(edgeColor);
        g.drawRect(1, 1, 13, 13);
        g.drawLine(1, 0, 14, 0);
        g.drawLine(15, 1, 15, 14);
        g.drawLine(1, 15, 14, 15);
        g.drawLine(0, 1, 0, 14);
        g.drawLine(2, 5, 13, 5);
        g.drawLine(3, 3, 3, 3);
        g.drawLine(6, 3, 6, 3);
        g.drawLine(9, 3, 9, 3);
        g.drawLine(12, 3, 12, 3);
        g.translate(-x, -y);
    }
    
    public int getIconWidth() {
        return 16;
    }
    
    public int getIconHeight() {
        return 16;
    }
}
