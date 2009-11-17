package javax.swing.plaf.metal;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;

class MetalIconFactory$VerticalSliderThumbIcon implements Icon, Serializable, UIResource {
    protected static MetalBumps controlBumps;
    protected static MetalBumps primaryBumps;
    
    public MetalIconFactory$VerticalSliderThumbIcon() {
        
        controlBumps = new MetalBumps(6, 10, MetalLookAndFeel.getControlHighlight(), MetalLookAndFeel.getControlInfo(), MetalLookAndFeel.getControl());
        primaryBumps = new MetalBumps(6, 10, MetalLookAndFeel.getPrimaryControl(), MetalLookAndFeel.getPrimaryControlDarkShadow(), MetalLookAndFeel.getPrimaryControlShadow());
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        JSlider slider = (JSlider)(JSlider)c;
        boolean leftToRight = MetalUtils.isLeftToRight(slider);
        g.translate(x, y);
        if (slider.hasFocus()) {
            g.setColor(MetalLookAndFeel.getPrimaryControlInfo());
        } else {
            g.setColor(slider.isEnabled() ? MetalLookAndFeel.getPrimaryControlInfo() : MetalLookAndFeel.getControlDarkShadow());
        }
        if (leftToRight) {
            g.drawLine(1, 0, 8, 0);
            g.drawLine(0, 1, 0, 13);
            g.drawLine(1, 14, 8, 14);
            g.drawLine(9, 1, 15, 7);
            g.drawLine(9, 13, 15, 7);
        } else {
            g.drawLine(7, 0, 14, 0);
            g.drawLine(15, 1, 15, 13);
            g.drawLine(7, 14, 14, 14);
            g.drawLine(0, 7, 6, 1);
            g.drawLine(0, 7, 6, 13);
        }
        if (slider.hasFocus()) {
            g.setColor(c.getForeground());
        } else {
            g.setColor(MetalLookAndFeel.getControl());
        }
        if (leftToRight) {
            g.fillRect(1, 1, 8, 13);
            g.drawLine(9, 2, 9, 12);
            g.drawLine(10, 3, 10, 11);
            g.drawLine(11, 4, 11, 10);
            g.drawLine(12, 5, 12, 9);
            g.drawLine(13, 6, 13, 8);
            g.drawLine(14, 7, 14, 7);
        } else {
            g.fillRect(7, 1, 8, 13);
            g.drawLine(6, 3, 6, 12);
            g.drawLine(5, 4, 5, 11);
            g.drawLine(4, 5, 4, 10);
            g.drawLine(3, 6, 3, 9);
            g.drawLine(2, 7, 2, 8);
        }
        int offset = (leftToRight) ? 2 : 8;
        if (slider.isEnabled()) {
            if (slider.hasFocus()) {
                primaryBumps.paintIcon(c, g, offset, 2);
            } else {
                controlBumps.paintIcon(c, g, offset, 2);
            }
        }
        if (slider.isEnabled()) {
            g.setColor(slider.hasFocus() ? MetalLookAndFeel.getPrimaryControl() : MetalLookAndFeel.getControlHighlight());
            if (leftToRight) {
                g.drawLine(1, 1, 8, 1);
                g.drawLine(1, 1, 1, 13);
            } else {
                g.drawLine(8, 1, 14, 1);
                g.drawLine(1, 7, 7, 1);
            }
        }
        g.translate(-x, -y);
    }
    
    public int getIconWidth() {
        return 16;
    }
    
    public int getIconHeight() {
        return 15;
    }
}
