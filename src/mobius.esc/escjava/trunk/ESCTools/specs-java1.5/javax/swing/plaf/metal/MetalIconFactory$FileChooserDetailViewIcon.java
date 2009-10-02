package javax.swing.plaf.metal;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;

class MetalIconFactory$FileChooserDetailViewIcon implements Icon, UIResource, Serializable {
    
    /*synthetic*/ MetalIconFactory$FileChooserDetailViewIcon(javax.swing.plaf.metal.MetalIconFactory$1 x0) {
        this();
    }
    
    private MetalIconFactory$FileChooserDetailViewIcon() {
        
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        g.translate(x, y);
        g.setColor(MetalLookAndFeel.getPrimaryControlInfo());
        g.drawLine(2, 2, 5, 2);
        g.drawLine(2, 3, 2, 7);
        g.drawLine(3, 7, 6, 7);
        g.drawLine(6, 6, 6, 3);
        g.drawLine(2, 10, 5, 10);
        g.drawLine(2, 11, 2, 15);
        g.drawLine(3, 15, 6, 15);
        g.drawLine(6, 14, 6, 11);
        g.drawLine(8, 5, 15, 5);
        g.drawLine(8, 13, 15, 13);
        g.setColor(MetalLookAndFeel.getPrimaryControl());
        g.drawRect(3, 3, 2, 3);
        g.drawRect(3, 11, 2, 3);
        g.setColor(MetalLookAndFeel.getPrimaryControlHighlight());
        g.drawLine(4, 4, 4, 5);
        g.drawLine(4, 12, 4, 13);
        g.translate(-x, -y);
    }
    
    public int getIconWidth() {
        return 18;
    }
    
    public int getIconHeight() {
        return 18;
    }
}
