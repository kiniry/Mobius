package javax.swing.plaf.metal;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;

class MetalIconFactory$TreeFloppyDriveIcon implements Icon, UIResource, Serializable {
    
    /*synthetic*/ MetalIconFactory$TreeFloppyDriveIcon(javax.swing.plaf.metal.MetalIconFactory$1 x0) {
        this();
    }
    
    private MetalIconFactory$TreeFloppyDriveIcon() {
        
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        g.translate(x, y);
        g.setColor(MetalLookAndFeel.getPrimaryControl());
        g.fillRect(2, 2, 12, 12);
        g.setColor(MetalLookAndFeel.getPrimaryControlInfo());
        g.drawLine(1, 1, 13, 1);
        g.drawLine(14, 2, 14, 14);
        g.drawLine(1, 14, 14, 14);
        g.drawLine(1, 1, 1, 14);
        g.setColor(MetalLookAndFeel.getControlDarkShadow());
        g.fillRect(5, 2, 6, 5);
        g.drawLine(4, 8, 11, 8);
        g.drawLine(3, 9, 3, 13);
        g.drawLine(12, 9, 12, 13);
        g.setColor(MetalLookAndFeel.getPrimaryControlHighlight());
        g.fillRect(8, 3, 2, 3);
        g.fillRect(4, 9, 8, 5);
        g.setColor(MetalLookAndFeel.getPrimaryControlShadow());
        g.drawLine(5, 10, 9, 10);
        g.drawLine(5, 12, 8, 12);
        g.translate(-x, -y);
    }
    
    public int getIconWidth() {
        return 16;
    }
    
    public int getIconHeight() {
        return 16;
    }
}
