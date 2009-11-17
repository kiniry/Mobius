package javax.swing.plaf.metal;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;

class MetalIconFactory$MenuArrowIcon implements Icon, UIResource, Serializable {
    
    /*synthetic*/ MetalIconFactory$MenuArrowIcon(javax.swing.plaf.metal.MetalIconFactory$1 x0) {
        this();
    }
    
    private MetalIconFactory$MenuArrowIcon() {
        
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        JMenuItem b = (JMenuItem)(JMenuItem)c;
        ButtonModel model = b.getModel();
        g.translate(x, y);
        if (!model.isEnabled()) {
            g.setColor(MetalLookAndFeel.getMenuDisabledForeground());
        } else {
            if (model.isArmed() || (c instanceof JMenu && model.isSelected())) {
                g.setColor(MetalLookAndFeel.getMenuSelectedForeground());
            } else {
                g.setColor(b.getForeground());
            }
        }
        if (MetalUtils.isLeftToRight(b)) {
            g.drawLine(0, 0, 0, 7);
            g.drawLine(1, 1, 1, 6);
            g.drawLine(2, 2, 2, 5);
            g.drawLine(3, 3, 3, 4);
        } else {
            g.drawLine(4, 0, 4, 7);
            g.drawLine(3, 1, 3, 6);
            g.drawLine(2, 2, 2, 5);
            g.drawLine(1, 3, 1, 4);
        }
        g.translate(-x, -y);
    }
    
    public int getIconWidth() {
        return MetalIconFactory.access$1800().width;
    }
    
    public int getIconHeight() {
        return MetalIconFactory.access$1800().height;
    }
}
