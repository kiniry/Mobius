package javax.swing.plaf.metal;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;

class MetalIconFactory$HorizontalSliderThumbIcon implements Icon, Serializable, UIResource {
    protected static MetalBumps controlBumps;
    protected static MetalBumps primaryBumps;
    
    public MetalIconFactory$HorizontalSliderThumbIcon() {
        
        controlBumps = new MetalBumps(10, 6, MetalLookAndFeel.getControlHighlight(), MetalLookAndFeel.getControlInfo(), MetalLookAndFeel.getControl());
        primaryBumps = new MetalBumps(10, 6, MetalLookAndFeel.getPrimaryControl(), MetalLookAndFeel.getPrimaryControlDarkShadow(), MetalLookAndFeel.getPrimaryControlShadow());
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        JSlider slider = (JSlider)(JSlider)c;
        g.translate(x, y);
        if (slider.hasFocus()) {
            g.setColor(MetalLookAndFeel.getPrimaryControlInfo());
        } else {
            g.setColor(slider.isEnabled() ? MetalLookAndFeel.getPrimaryControlInfo() : MetalLookAndFeel.getControlDarkShadow());
        }
        g.drawLine(1, 0, 13, 0);
        g.drawLine(0, 1, 0, 8);
        g.drawLine(14, 1, 14, 8);
        g.drawLine(1, 9, 7, 15);
        g.drawLine(7, 15, 14, 8);
        if (slider.hasFocus()) {
            g.setColor(c.getForeground());
        } else {
            g.setColor(MetalLookAndFeel.getControl());
        }
        g.fillRect(1, 1, 13, 8);
        g.drawLine(2, 9, 12, 9);
        g.drawLine(3, 10, 11, 10);
        g.drawLine(4, 11, 10, 11);
        g.drawLine(5, 12, 9, 12);
        g.drawLine(6, 13, 8, 13);
        g.drawLine(7, 14, 7, 14);
        if (slider.isEnabled()) {
            if (slider.hasFocus()) {
                primaryBumps.paintIcon(c, g, 2, 2);
            } else {
                controlBumps.paintIcon(c, g, 2, 2);
            }
        }
        if (slider.isEnabled()) {
            g.setColor(slider.hasFocus() ? MetalLookAndFeel.getPrimaryControl() : MetalLookAndFeel.getControlHighlight());
            g.drawLine(1, 1, 13, 1);
            g.drawLine(1, 1, 1, 8);
        }
        g.translate(-x, -y);
    }
    
    public int getIconWidth() {
        return 15;
    }
    
    public int getIconHeight() {
        return 16;
    }
}
