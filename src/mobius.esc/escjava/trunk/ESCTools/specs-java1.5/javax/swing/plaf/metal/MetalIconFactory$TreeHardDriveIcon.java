package javax.swing.plaf.metal;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;

class MetalIconFactory$TreeHardDriveIcon implements Icon, UIResource, Serializable {
    
    /*synthetic*/ MetalIconFactory$TreeHardDriveIcon(javax.swing.plaf.metal.MetalIconFactory$1 x0) {
        this();
    }
    
    private MetalIconFactory$TreeHardDriveIcon() {
        
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        g.translate(x, y);
        g.setColor(MetalLookAndFeel.getPrimaryControlInfo());
        g.drawLine(1, 4, 1, 5);
        g.drawLine(2, 3, 3, 3);
        g.drawLine(4, 2, 11, 2);
        g.drawLine(12, 3, 13, 3);
        g.drawLine(14, 4, 14, 5);
        g.drawLine(12, 6, 13, 6);
        g.drawLine(4, 7, 11, 7);
        g.drawLine(2, 6, 3, 6);
        g.drawLine(1, 7, 1, 8);
        g.drawLine(2, 9, 3, 9);
        g.drawLine(4, 10, 11, 10);
        g.drawLine(12, 9, 13, 9);
        g.drawLine(14, 7, 14, 8);
        g.drawLine(1, 10, 1, 11);
        g.drawLine(2, 12, 3, 12);
        g.drawLine(4, 13, 11, 13);
        g.drawLine(12, 12, 13, 12);
        g.drawLine(14, 10, 14, 11);
        g.setColor(MetalLookAndFeel.getControlShadow());
        g.drawLine(7, 6, 7, 6);
        g.drawLine(9, 6, 9, 6);
        g.drawLine(10, 5, 10, 5);
        g.drawLine(11, 6, 11, 6);
        g.drawLine(12, 5, 13, 5);
        g.drawLine(13, 4, 13, 4);
        g.drawLine(7, 9, 7, 9);
        g.drawLine(9, 9, 9, 9);
        g.drawLine(10, 8, 10, 8);
        g.drawLine(11, 9, 11, 9);
        g.drawLine(12, 8, 13, 8);
        g.drawLine(13, 7, 13, 7);
        g.drawLine(7, 12, 7, 12);
        g.drawLine(9, 12, 9, 12);
        g.drawLine(10, 11, 10, 11);
        g.drawLine(11, 12, 11, 12);
        g.drawLine(12, 11, 13, 11);
        g.drawLine(13, 10, 13, 10);
        g.setColor(MetalLookAndFeel.getControlHighlight());
        g.drawLine(4, 3, 5, 3);
        g.drawLine(7, 3, 9, 3);
        g.drawLine(11, 3, 11, 3);
        g.drawLine(2, 4, 6, 4);
        g.drawLine(8, 4, 8, 4);
        g.drawLine(2, 5, 3, 5);
        g.drawLine(4, 6, 4, 6);
        g.drawLine(2, 7, 3, 7);
        g.drawLine(2, 8, 3, 8);
        g.drawLine(4, 9, 4, 9);
        g.drawLine(2, 10, 3, 10);
        g.drawLine(2, 11, 3, 11);
        g.drawLine(4, 12, 4, 12);
        g.translate(-x, -y);
    }
    
    public int getIconWidth() {
        return 16;
    }
    
    public int getIconHeight() {
        return 16;
    }
}
