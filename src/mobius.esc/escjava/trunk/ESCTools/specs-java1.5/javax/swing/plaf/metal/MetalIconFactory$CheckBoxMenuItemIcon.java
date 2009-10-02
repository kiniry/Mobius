package javax.swing.plaf.metal;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;

class MetalIconFactory$CheckBoxMenuItemIcon implements Icon, UIResource, Serializable {
    
    /*synthetic*/ MetalIconFactory$CheckBoxMenuItemIcon(javax.swing.plaf.metal.MetalIconFactory$1 x0) {
        this();
    }
    
    private MetalIconFactory$CheckBoxMenuItemIcon() {
        
    }
    
    public void paintOceanIcon(Component c, Graphics g, int x, int y) {
        ButtonModel model = ((JMenuItem)(JMenuItem)c).getModel();
        boolean isSelected = model.isSelected();
        boolean isEnabled = model.isEnabled();
        boolean isPressed = model.isPressed();
        boolean isArmed = model.isArmed();
        g.translate(x, y);
        if (isEnabled) {
            MetalUtils.drawGradient(c, g, "CheckBoxMenuItem.gradient", 1, 1, 7, 7, true);
            if (isPressed || isArmed) {
                g.setColor(MetalLookAndFeel.getControlInfo());
                g.drawLine(0, 0, 8, 0);
                g.drawLine(0, 0, 0, 8);
                g.drawLine(8, 2, 8, 8);
                g.drawLine(2, 8, 8, 8);
                g.setColor(MetalLookAndFeel.getPrimaryControl());
                g.drawLine(9, 1, 9, 9);
                g.drawLine(1, 9, 9, 9);
            } else {
                g.setColor(MetalLookAndFeel.getControlDarkShadow());
                g.drawLine(0, 0, 8, 0);
                g.drawLine(0, 0, 0, 8);
                g.drawLine(8, 2, 8, 8);
                g.drawLine(2, 8, 8, 8);
                g.setColor(MetalLookAndFeel.getControlHighlight());
                g.drawLine(9, 1, 9, 9);
                g.drawLine(1, 9, 9, 9);
            }
        } else {
            g.setColor(MetalLookAndFeel.getMenuDisabledForeground());
            g.drawRect(0, 0, 8, 8);
        }
        if (isSelected) {
            if (isEnabled) {
                if (isArmed || (c instanceof JMenu && isSelected)) {
                    g.setColor(MetalLookAndFeel.getMenuSelectedForeground());
                } else {
                    g.setColor(c.getForeground());
                }
            } else {
                g.setColor(MetalLookAndFeel.getMenuDisabledForeground());
            }
            g.drawLine(2, 2, 2, 6);
            g.drawLine(3, 2, 3, 6);
            g.drawLine(4, 4, 8, 0);
            g.drawLine(4, 5, 9, 0);
        }
        g.translate(-x, -y);
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        if (MetalLookAndFeel.usingOcean()) {
            paintOceanIcon(c, g, x, y);
            return;
        }
        JMenuItem b = (JMenuItem)(JMenuItem)c;
        ButtonModel model = b.getModel();
        boolean isSelected = model.isSelected();
        boolean isEnabled = model.isEnabled();
        boolean isPressed = model.isPressed();
        boolean isArmed = model.isArmed();
        g.translate(x, y);
        if (isEnabled) {
            if (isPressed || isArmed) {
                g.setColor(MetalLookAndFeel.getControlInfo());
                g.drawLine(0, 0, 8, 0);
                g.drawLine(0, 0, 0, 8);
                g.drawLine(8, 2, 8, 8);
                g.drawLine(2, 8, 8, 8);
                g.setColor(MetalLookAndFeel.getPrimaryControl());
                g.drawLine(1, 1, 7, 1);
                g.drawLine(1, 1, 1, 7);
                g.drawLine(9, 1, 9, 9);
                g.drawLine(1, 9, 9, 9);
            } else {
                g.setColor(MetalLookAndFeel.getControlDarkShadow());
                g.drawLine(0, 0, 8, 0);
                g.drawLine(0, 0, 0, 8);
                g.drawLine(8, 2, 8, 8);
                g.drawLine(2, 8, 8, 8);
                g.setColor(MetalLookAndFeel.getControlHighlight());
                g.drawLine(1, 1, 7, 1);
                g.drawLine(1, 1, 1, 7);
                g.drawLine(9, 1, 9, 9);
                g.drawLine(1, 9, 9, 9);
            }
        } else {
            g.setColor(MetalLookAndFeel.getMenuDisabledForeground());
            g.drawRect(0, 0, 8, 8);
        }
        if (isSelected) {
            if (isEnabled) {
                if (model.isArmed() || (c instanceof JMenu && model.isSelected())) {
                    g.setColor(MetalLookAndFeel.getMenuSelectedForeground());
                } else {
                    g.setColor(b.getForeground());
                }
            } else {
                g.setColor(MetalLookAndFeel.getMenuDisabledForeground());
            }
            g.drawLine(2, 2, 2, 6);
            g.drawLine(3, 2, 3, 6);
            g.drawLine(4, 4, 8, 0);
            g.drawLine(4, 5, 9, 0);
        }
        g.translate(-x, -y);
    }
    
    public int getIconWidth() {
        return MetalIconFactory.access$1900().width;
    }
    
    public int getIconHeight() {
        return MetalIconFactory.access$1900().height;
    }
}
