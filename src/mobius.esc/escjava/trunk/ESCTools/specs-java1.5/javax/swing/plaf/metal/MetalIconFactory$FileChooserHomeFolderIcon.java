package javax.swing.plaf.metal;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;

class MetalIconFactory$FileChooserHomeFolderIcon implements Icon, UIResource, Serializable {
    
    /*synthetic*/ MetalIconFactory$FileChooserHomeFolderIcon(javax.swing.plaf.metal.MetalIconFactory$1 x0) {
        this();
    }
    
    private MetalIconFactory$FileChooserHomeFolderIcon() {
        
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        g.translate(x, y);
        g.setColor(MetalLookAndFeel.getPrimaryControlInfo());
        g.drawLine(8, 1, 1, 8);
        g.drawLine(8, 1, 15, 8);
        g.drawLine(11, 2, 11, 3);
        g.drawLine(12, 2, 12, 4);
        g.drawLine(3, 7, 3, 15);
        g.drawLine(13, 7, 13, 15);
        g.drawLine(4, 15, 12, 15);
        g.drawLine(6, 9, 6, 14);
        g.drawLine(10, 9, 10, 14);
        g.drawLine(7, 9, 9, 9);
        g.setColor(MetalLookAndFeel.getControlDarkShadow());
        g.fillRect(8, 2, 1, 1);
        g.fillRect(7, 3, 3, 1);
        g.fillRect(6, 4, 5, 1);
        g.fillRect(5, 5, 7, 1);
        g.fillRect(4, 6, 9, 2);
        g.drawLine(9, 12, 9, 12);
        g.setColor(MetalLookAndFeel.getPrimaryControl());
        g.drawLine(4, 8, 12, 8);
        g.fillRect(4, 9, 2, 6);
        g.fillRect(11, 9, 2, 6);
        g.translate(-x, -y);
    }
    
    public int getIconWidth() {
        return 18;
    }
    
    public int getIconHeight() {
        return 18;
    }
}
