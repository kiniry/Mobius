package javax.swing.plaf.metal;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;

class MetalIconFactory$TreeComputerIcon implements Icon, UIResource, Serializable {
    
    /*synthetic*/ MetalIconFactory$TreeComputerIcon(javax.swing.plaf.metal.MetalIconFactory$1 x0) {
        this();
    }
    
    private MetalIconFactory$TreeComputerIcon() {
        
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        g.translate(x, y);
        g.setColor(MetalLookAndFeel.getPrimaryControl());
        g.fillRect(5, 4, 6, 4);
        g.setColor(MetalLookAndFeel.getPrimaryControlInfo());
        g.drawLine(2, 2, 2, 8);
        g.drawLine(13, 2, 13, 8);
        g.drawLine(3, 1, 12, 1);
        g.drawLine(12, 9, 12, 9);
        g.drawLine(3, 9, 3, 9);
        g.drawLine(4, 4, 4, 7);
        g.drawLine(5, 3, 10, 3);
        g.drawLine(11, 4, 11, 7);
        g.drawLine(5, 8, 10, 8);
        g.drawLine(1, 10, 14, 10);
        g.drawLine(14, 10, 14, 14);
        g.drawLine(1, 14, 14, 14);
        g.drawLine(1, 10, 1, 14);
        g.setColor(MetalLookAndFeel.getControlDarkShadow());
        g.drawLine(6, 12, 8, 12);
        g.drawLine(10, 12, 12, 12);
        g.translate(-x, -y);
    }
    
    public int getIconWidth() {
        return 16;
    }
    
    public int getIconHeight() {
        return 16;
    }
}
